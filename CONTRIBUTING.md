# Contributing

All places to contribute, and spaces in general, are governed by our
[Code of Conduct](/Code of Conduct.md).

This document will specifically focus on contributions to this repository and
the files present here however, in the form of writing code. For contributions
to this repository regarding documentation, we don't currently have specific
guidelines other than the sections of this document which remain relevant.

### Contributing Commits

Commits should be submitted via a pull request to our
[GitHub repository](https://github.com/kayabaNerve/trout). Exceptionally, patch
files may be emailed to
[`patches@serai.exchange`](mailto:patches@serai.exchange).

Commits will be checked against our Continuous Integration, orchestrated via
GitHub Actions and ran by GitHub's provided runners for public repositories.
These will perform a myriad of static analyses and ran applicable tests. These
SHOULD be run locally _before_ making a pull request. As a rule of thumb,

```sh
cargo +nightly fmt
cargo +nightly clippy --all-features --all-targets
```

should not effect any change nor yield any warnings/errors due to your changes.

All contributions _MUST_ follow the terms within our
[licensing policies](/LICENSE.md).
