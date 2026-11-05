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

## Follow-up: pre-close negative-control distinction

The original real-filesystem RLIMIT_FSIZE probe passed on both the historical
unfixed source and repaired source. It therefore did not isolate the hPut
failure point: an exception during hClose can close the descriptor already.

The stronger regression verifies the pinned original source blob
`ccc9e975be0ee318e333808387217c71d8217af5` at commit
`9ad035731fc4c87c5be2aba7e4bc589b738f1231`. It compiles isolated
copies of the original and repaired module, each instrumented in temporary
test-only source at exactly one hPut call with an identifying IOException.
The source checkout and public interfaces are unmodified. GHC must compile
the instrumented source path.

The original must fail specifically because its descriptor is still open
after that pre-close exception; the repaired module must pass and retry in
the same process. The real RLIMIT failure remains a separate positive
control, not evidence about which write/flush operation threw. This is a
bounded Linux/GHC regression rather than proof of all exception cases.

## Strong handle reference and retry harness correction

The first injected test was inconclusive: the unmodified baseline passed the
open-descriptor scan, and the later retry failed because every test-module
`hPut` was deliberately faulted. The revised test holds the acquired Handle
in a test-only `IORef` and queries `hIsClosed` through a CPP-enabled worker,
so an opportunistic finalizer cannot conceal the missing explicit close.

The injected variant tests only the one forced failure. The independent
uninstrumented `RLIMIT_FSIZE` case continues to verify successful same-process
retry and no-replace behavior. The baseline must specifically fail because its
anchored handle is still open, while the repaired source must pass.
