# Provider-relative Path implementation refinement v1

`PHIL-P1-IO-PATH-001` is certified in Rocq by `ProviderRelativePath.v` and `ProviderRelativePathImplementation.v`. This refinement slice narrows the remaining implementation trust boundary by extracting the ordered admission decision and routing production through that exact kernel.

## Certified semantic authority

The extracted kernel owns:

- rejection of an empty `FileSystem` occurrence;
- empty raw path rejection before absolute-source-root rejection;
- source-leading `/` rejection before segment validation;
- left-to-right segment validation;
- within a segment, empty rejection before `.`, then `..`, otherwise acceptance; and
- exact one-based rejection indices.

Production may not reorder or bypass these decisions.

## Native representation boundary

The following remain native Haskell facts and are supplied to the kernel rather than proved by it:

- `Data.Text` scalar representation;
- `Text.null`;
- `Text.isPrefixOf` for source `/`;
- `Text.splitOn "/"`;
- comparison of a segment with `.` and `..`;
- reconstruction of the existing typed diagnostic payloads; and
- preservation/rendering of the original accepted `Text` segments.

Host separators, drive syntax, current working directory, Unicode normalization, symlink policy, and host filesystem semantics are not inputs to the certified decision and therefore cannot acquire source-level authority through this boundary.

## Production correspondence

`src/Phil/Systems.hs` computes the representation facts, calls `ProviderRelativePathKernel`, and reconstructs the existing result. The accepted result stores the original provider occurrence and exact `Text.splitOn "/"` segments; the extracted kernel never rewrites path content.

Direct kernel controls exercise every ordered branch plus left-to-right rejection indexing. The unchanged IO-PATH corpus remains the end-to-end pressure test.
