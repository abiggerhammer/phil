# PHIL-P1-IO-PATH-001 proof boundary

This slice certifies the implementation semantics of canonical provider-relative `Path` values without importing ambient host filesystem meaning into Phil.

The Rocq semantic model owns:

- exact FileSystem occurrence qualification as part of path identity;
- nonempty occurrence identity;
- nonempty path segment lists;
- exclusion of empty, `.` and `..` source segments;
- exact preservation of accepted segment scalar sequences; and
- non-collapse of equal spellings across distinct provider occurrences.

The executable implementation-correspondence model owns the production rejection order:

1. empty FileSystem occurrence rejects;
2. empty path rejects before the absolute-source-root check;
3. leading source `/` rejects before segment validation;
4. segments are checked left-to-right;
5. within a segment, empty rejects before `.`, and `.` before `..`.

Concrete `Data.Text` scalar representation, `Text.null`, `Text.isPrefixOf`, `Text.splitOn "/"`, and the correspondence from those operations to the representation-neutral boolean facts remain explicit native implementation facts. Host separators, drive spelling, current working directory, symlink policy, normalization, and host absolute-path conventions are not semantic inputs.

A later implementation-refinement closeout may extract and production-bind the owned ordered decision surface after this certification slice lands cleanly.
