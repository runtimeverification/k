---
copyright: Copyright (c) K Team. All Rights Reserved.
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
tag [@baltoli][bruce] as a fallback.

Once your code has been reviewed by a K maintainer, we will open a new PR that
includes your commits with [proper attribution][authors]. Doing so allows us to
run our internal CI processes once we are happy with your code. If the tests
pass, we will merge the PR and close your original PR. If changes need to be
made subsequently to get tests to pass, they will need to be pushed to your
original fork branch.

### Licensing

K is licensed under the [BSD 3-Clause License][license]. If you make changes to
K via a pull request, your changes will automatically be licensed under the same
license following [Github's terms of service][tos].

### For RV Maintainers

If you are an RV-internal K developer, please take ownership of any community
pull requests you review, and make sure that they end up getting merged promptly
following these instructions.

First, review the code in the original PR as you would normally. If you are
happy with the changes made, then create a new branch of your local K repo
referencing the external PR number:
```console
$ git checkout -b adopt-pr-$NUMBER
```

Then, add the external user's fork to your local repo as a remote:
```console
$ git remote add temp-k-fork https://github.com/$USER/k.git
$ git fetch temp-k-fork
```

You can now cherry-pick the commit range in the user's PR onto your local
branch:
```console
$ git cherry-pick $START..$END
```

Finally, push your branch to `runtimeverification/k` and open a PR as usual. CI
should run as expected, and you can request a secondary RV-internal code review
as you would for one of your own PRs. Double-check that the external user is
credited as the commit author in the Github UI.

If further changes need to be made by the external user, you can cherry-pick
their changes over to your branch as before.

Once your duplicated PR is merged, you can close (not merge) the user's original
PR and remove your remote pointing to their fork.
```console
$ git remote rm temp-k-fork
```

[authors]: https://docs.github.com/en/pull-requests/committing-changes-to-your-project/creating-and-editing-commits/creating-a-commit-with-multiple-authors
[bruce]: https://github.com/baltoli
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
