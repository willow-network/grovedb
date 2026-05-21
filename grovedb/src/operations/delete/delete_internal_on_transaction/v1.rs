//! `delete_internal_on_transaction` v1 — grove v3+ dispatch path.
//!
//! Fixes issue #686: when deleting a non-empty tree element, the parent layer
//! is no longer reopened with the *child* tree type. Instead the already-open
//! parent merk (`subtree_to_delete_from`) is reused, so aggregate/root
//! propagation uses the parent tree type. The historical behavior is preserved
//! in [`super::v0`](super::v0) for grove v1/v2 replay compatibility.

use std::collections::HashMap;

use grovedb_costs::{
    cost_return_on_error, cost_return_on_error_into, storage_cost::removal::StorageRemovedBytes,
    CostResult, CostsExt, OperationCost,
};
use grovedb_merk::{
    element::{delete::ElementDeleteFromStorageExtensions, tree_type::ElementTreeTypeExtensions},
    Error as MerkError, Merk,
};
use grovedb_path::SubtreePath;
use grovedb_storage::{
    rocksdb_storage::PrefixedRocksDbTransactionContext, Storage, StorageBatch, StorageContext,
};
use grovedb_version::version::GroveVersion;

use super::super::DeleteOptions;
use crate::{Element, Error, GroveDb, Transaction};

impl GroveDb {
    pub(super) fn delete_internal_on_transaction_v1<B: AsRef<[u8]>>(
        &self,
        path: SubtreePath<B>,
        key: &[u8],
        options: &DeleteOptions,
        transaction: &Transaction,
        sectioned_removal: &mut impl FnMut(
            &Vec<u8>,
            u32,
            u32,
        ) -> Result<
            (StorageRemovedBytes, StorageRemovedBytes),
            MerkError,
        >,
        batch: &StorageBatch,
        grove_version: &GroveVersion,
    ) -> CostResult<bool, Error> {
        let mut cost = OperationCost::default();

        let element = cost_return_on_error!(
            &mut cost,
            self.get_raw(path.clone(), key.as_ref(), Some(transaction), grove_version)
        );
        let mut subtree_to_delete_from = cost_return_on_error!(
            &mut cost,
            self.open_transactional_merk_at_path(
                path.clone(),
                transaction,
                Some(batch),
                grove_version
            )
        );
        let parent_tree_type = subtree_to_delete_from.tree_type;
        if element.tree_type().is_some() {
            let subtree_merk_path = path.derive_owned_with_child(key);
            let subtree_merk_path_ref = SubtreePath::from(&subtree_merk_path);

            // Tree types that store data in the data namespace as non-Merk
            // entries (CommitmentTree, MmrTree, BulkAppendTree, DenseTree)
            // have an always-empty Merk but may have data.  We cannot iterate
            // their storage with find_subtrees because the entries are not
            // valid Element serializations.
            let non_merk_data = element.uses_non_merk_data_storage();

            let subtree_of_tree_we_are_deleting = cost_return_on_error!(
                &mut cost,
                self.open_transactional_merk_at_path(
                    subtree_merk_path_ref.clone(),
                    transaction,
                    Some(batch),
                    grove_version,
                )
            );

            // For non-Merk data trees the raw_iter check would see non-Merk
            // keys and wrongly report the tree as non-empty.  Use the
            // element's own count instead.
            let is_empty = if non_merk_data {
                element.non_merk_entry_count().unwrap_or(0) == 0
            } else {
                subtree_of_tree_we_are_deleting
                    .is_empty_tree()
                    .unwrap_add_cost(&mut cost)
            };

            if !options.allow_deleting_non_empty_trees && !is_empty {
                return if options.deleting_non_empty_trees_returns_error {
                    Err(Error::DeletingNonEmptyTree(
                        "trying to do a delete operation for a non empty tree, but options not \
                         allowing this",
                    ))
                    .wrap_with_cost(cost)
                } else {
                    Ok(false).wrap_with_cost(cost)
                };
            }

            if !is_empty {
                if non_merk_data {
                    // Non-Merk data trees: clear the subtree storage directly.
                    // These trees never contain child subtrees so we only need
                    // to clear the one storage context.
                    let mut storage = self
                        .db
                        .get_transactional_storage_context(
                            subtree_merk_path_ref.clone(),
                            Some(batch),
                            transaction,
                        )
                        .unwrap_add_cost(&mut cost);
                    cost_return_on_error!(
                        &mut cost,
                        storage.clear().map_err(|e| {
                            Error::CorruptedData(format!(
                                "unable to cleanup non-merk tree data from storage: {e}",
                            ))
                        })
                    );
                } else {
                    let subtrees_paths = cost_return_on_error!(
                        &mut cost,
                        self.find_subtrees(
                            &subtree_merk_path_ref,
                            Some(transaction),
                            grove_version
                        )
                    );
                    for subtree_path in subtrees_paths {
                        let p: SubtreePath<_> = subtree_path.as_slice().into();
                        let mut storage = self
                            .db
                            .get_transactional_storage_context(p, Some(batch), transaction)
                            .unwrap_add_cost(&mut cost);

                        cost_return_on_error!(
                            &mut cost,
                            storage.clear().map_err(|e| {
                                Error::CorruptedData(format!(
                                    "unable to cleanup tree from storage: {e}",
                                ))
                            })
                        );
                    }
                }
                // Reuse the already-open parent merk so propagation keeps the
                // parent tree type instead of reopening with the child type.
                // We are deleting a tree, a tree uses 3 bytes
                cost_return_on_error_into!(
                    &mut cost,
                    Element::delete_with_sectioned_removal_bytes(
                        &mut subtree_to_delete_from,
                        key,
                        Some(options.as_merk_options()),
                        true,
                        parent_tree_type,
                        sectioned_removal,
                        grove_version,
                    )
                );
                let mut merk_cache: HashMap<
                    SubtreePath<B>,
                    Merk<PrefixedRocksDbTransactionContext>,
                > = HashMap::default();
                merk_cache.insert(path.clone(), subtree_to_delete_from);
                cost_return_on_error!(
                    &mut cost,
                    self.propagate_changes_with_batch_transaction(
                        batch,
                        merk_cache,
                        &path,
                        transaction,
                        grove_version,
                    )
                );
            } else {
                // We are deleting a tree, a tree uses 3 bytes
                cost_return_on_error_into!(
                    &mut cost,
                    Element::delete_with_sectioned_removal_bytes(
                        &mut subtree_to_delete_from,
                        key,
                        Some(options.as_merk_options()),
                        true,
                        parent_tree_type,
                        sectioned_removal,
                        grove_version,
                    )
                );
                let mut merk_cache: HashMap<
                    SubtreePath<B>,
                    Merk<PrefixedRocksDbTransactionContext>,
                > = HashMap::default();
                merk_cache.insert(path.clone(), subtree_to_delete_from);
                cost_return_on_error!(
                    &mut cost,
                    self.propagate_changes_with_transaction(
                        merk_cache,
                        path,
                        transaction,
                        batch,
                        grove_version
                    )
                );
            }
        } else {
            cost_return_on_error_into!(
                &mut cost,
                Element::delete_with_sectioned_removal_bytes(
                    &mut subtree_to_delete_from,
                    key,
                    Some(options.as_merk_options()),
                    false,
                    parent_tree_type,
                    sectioned_removal,
                    grove_version,
                )
            );
            let mut merk_cache: HashMap<SubtreePath<B>, Merk<PrefixedRocksDbTransactionContext>> =
                HashMap::default();
            merk_cache.insert(path.clone(), subtree_to_delete_from);
            cost_return_on_error!(
                &mut cost,
                self.propagate_changes_with_transaction(
                    merk_cache,
                    path,
                    transaction,
                    batch,
                    grove_version
                )
            );
        }

        Ok(true).wrap_with_cost(cost)
    }
}
