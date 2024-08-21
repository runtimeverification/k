---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# K Framework Contributor Guide

Thank you for making a contribution to the K Framework. This document explains
the steps that need to be followed to get your changes reviewed, tested and
merged into K. If you have any questions about this process or K in general,
please get in touch via our [Discord Server][discord] or [Matrix Room][matrix].

## Opening an issue

If you are using K and want to report something that doesn't work as you expect,
the best way to do so is to [open an issue][issue] against the [K repository][k-repo].
Please make sure to include as much relevant information as possible in your
issue to help us reproduce it. We will reply to you with any questions we have
about the issue, then triage it to get fixed.

## Making a change to K

We welcome contributions to K from the community. Because running the K test
suite uses our private compute resources, there are a few steps to go through to
get your changes tested and merged.

### Fork the K repository

For external contributors, please [fork][fork] the K repository following the
Github documentation. Commit any changes you make to a branch on your fork.

### Develop your changes locally

The first step is to develop and test your changes locally. Follow the
instructions in the [K README][readme] to build and test the project with your
changes included. The most important tests to run are the
[K integration tests][integration]:
```console
$ make -C k-distribution/tests/regression-new --jobs $(nproc) --output-sync
```

If your changes only apply to documentation, you can skip the testing phase.

### Open a pull request

Once you have tested your change locally, push your commits to your fork of K
and [open a pull request (PR)][pr], again following the Github documentation. In
the pull request, please indicate what tests you have run locally on your
changes (e.g. "I have run the K integration tests locally"). Because this PR is
coming from an external fork, the K test suite and CI process will not run. This
is expected behaviour. Additionally, please make sure that the commit history in
your PR is clean by [rebasing][rebase] any messy or partial commits. Finally, it
is important that your commits are based on the K `develop` branch.

Next, please request a review from a K maintainer on your PR. The last person to
modify the files you are changing is a good start, or if you're not sure,
tag [@tothtamas28][tamas] as a fallback.

Once your code has been initially reviewed by a K maintainer, we will approve it
to run against our CI test suite. If the tests pass, we will merge the PR and
close your original PR. If changes need to be made subsequently to get tests to
pass, they will need to be pushed to your original fork branch. For trivial
changes, it can be useful if you permit modifications to be pushed to your
branch by maintainers.

### Licensing

K is licensed under the [BSD 3-Clause License][license]. If you make changes to
K via a pull request, your changes will automatically be licensed under the same
license following [Github's terms of service][tos].


[authors]: https://docs.github.com/en/pull-requests/committing-changes-to-your-project/creating-and-editing-commits/creating-a-commit-with-multiple-authors
[tamas]: https://github.com/tothtamas28
[discord]: https://discord.com/invite/CurfmXNtbN
[fork]: https://docs.github.com/en/get-started/quickstart/fork-a-repo
[integration]: https://github.com/runtimeverification/k/tree/master/k-distribution/tests/regression-new
[issue]: https://github.com/runtimeverification/k/issues/new?assignees=&labels=k-bug%2Ck&template=bug-report.yaml&title=%5BK-Bug%5D+%3CTITLE%3E
[k-repo]: https://github.com/runtimeverification/k
[license]: https://github.com/runtimeverification/k/blob/master/LICENSE.md
[matrix]: https://matrix.to/#/#k:matrix.org
[pr]: https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/about-pull-requests
[readme]: https://github.com/runtimeverification/k/blob/master/README.md
[rebase]: https://docs.github.com/en/get-started/using-git/about-git-rebase
[tos]: https://docs.github.com/en/site-policy/github-terms/github-terms-of-service#6-contributions-under-repository-license
