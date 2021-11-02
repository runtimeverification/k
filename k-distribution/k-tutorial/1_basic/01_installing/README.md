# Lesson 1.1: Setting up a K Environment

The first step to learning K is to install K on your system, and configure your
editor for K development.

## Installing K

You have two options for how to install K, depending on how you intend to
interact with the K codebase. If you are solely a user of K, and have no
interest in developing or making changes to K, you most likely will want to
install one of our binary releases of K. However, if you are going to be a K
developer, or simply want to build K from source, you should follow the
instructions for a source build of K.

### Installing K from a binary release

K is developed as a rolling release, with each change to K that passes our
CI infrastructure being deployed on GitHub for download. The latest release of
K can be downloaded [here](https://github.com/kframework/k/releases/latest).
This page also contains information on how to install K. It is recommended
that you fully uninstall the old version of K prior to installing the new one,
as K does not maintain entries in package manager databases, with the exception
of Homebrew on MacOS.

### Installing K from source

You can clone K from GitHub with the following Git command:

```
git clone https://github.com/kframework/k --recursive
```

Instructions on how to build K from source can be found
[here](https://github.com/kframework/k/blob/master/README.md).

## Configuring your editor

K maintains a set of scripts for a variety of text editors, including vim and
emacs, in various states of maintenance. You can download these scripts with
the following Git command:

```
git clone https://github.com/kframework/k-editor-support
```

Because K allows users to define their own grammars for parsing K itself,
not all features of K can be effectively highlighted. However, at the cost of
occasionally highlighting things incorrectly, you can get some pretty good
results in many cases. With that being said, some of the editor scripts in the
above repository are pretty out of date. If you manage to improve them, we
welcome pull requests into the repository.

## Troubleshooting

If you have problems installing K, we encourage you to reach out to us. If you
follow the above install instructions and run into a problem, you can
[Create a bug report on GitHub](https://github.com/kframework/k/issues/new?assignees=&labels=bug&template=bug-report.md&title=%5BBug%5D+%5Bkompile%7Ckast%7Ckrun%7Ckprove%7Cksearch%5D+-+DESCRIPTION)

## Next lesson

Once you have set up K on your system to your satisfaction, you can continue to
[Lesson 1.2: Basics of Functional K](../02_basics/README.md).
