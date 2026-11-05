# E-STEVE-CLEANUP-01 — CAS temporary-handle lifetime

Bounded implementation follow-through of the independently recorded CAS
question. The separate user-file replacement repair remains closed.

The original installBlob attempts ByteString.hPut then hClose on a staged file.
An hPut exception before close skips deterministic handle closure, even though
its error path unlinks the temporary pathname.

The intended repair closes the acquired handle if hPut throws, while preserving
the *original* write error. Digest mismatch rejection, link-based no-overwrite
publication, Installed/AlreadyExists, and unlink cleanup remain unchanged.

The focused Linux/GHC 9.6.7 regression forces a real large ByteString write
failure under RLIMIT_FSIZE=0 with SIGXFSZ ignored. The *same process* examines
/proc/self/fd immediately for still-open CAS temporary descriptors, checks
absence of temporary names or accidental publication, and retries an empty
install successfully without process exit. A large RTS nursery discourages
GC finalizers from masking an open-handle defect.

This does not establish crash durability, a full asynchronous-interruption
contract, hostile-directory policy, read-size limits or provider-wide proof.
