//! Versioned dispatch for [`GroveDb::delete_internal_on_transaction`].
//!
//! Each `v*.rs` defines one `delete_internal_on_transaction_v*` method. The
//! dispatcher below selects the implementation by
//! `GroveVersion::grovedb_versions.operations.delete.delete_internal_on_transaction`.
//!
//! `v0` preserves the historical (grove v1/v2) behavior: when deleting a
//! non-empty tree it reopened the parent layer using the *child* tree type,
//! which propagated parent aggregate (count/sum) metadata incorrectly. `v1`
//! (grove v3+) reuses the already-open parent merk so propagation uses the
//! parent tree type. See issue #686.

mod v0;
mod v1;

use grovedb_costs::{
    storage_cost::removal::StorageRemovedBytes, CostResult, CostsExt, OperationCost,
};
use grovedb_merk::Error as MerkError;
use grovedb_path::SubtreePath;
use grovedb_storage::StorageBatch;
use grovedb_version::{error::GroveVersionError, version::GroveVersion};

use super::DeleteOptions;
use crate::{Error, GroveDb, Transaction};

impl GroveDb {
    pub(super) fn delete_internal_on_transaction<B: AsRef<[u8]>>(
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
        match grove_version
            .grovedb_versions
            .operations
            .delete
            .delete_internal_on_transaction
        {
            0 => self.delete_internal_on_transaction_v0(
                path,
                key,
                options,
                transaction,
                sectioned_removal,
                batch,
                grove_version,
            ),
            1 => self.delete_internal_on_transaction_v1(
                path,
                key,
                options,
                transaction,
                sectioned_removal,
                batch,
                grove_version,
            ),
            version => Err(Error::VersionError(
                GroveVersionError::UnknownVersionMismatch {
                    method: "delete_internal_on_transaction".to_string(),
                    known_versions: vec![0, 1],
                    received: version,
                },
            ))
            .wrap_with_cost(OperationCost::default()),
        }
    }
}
