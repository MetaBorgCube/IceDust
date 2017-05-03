# Language extensions

Applying IceDust in a specific domain usually requires extending IceDust with language features that do not make sense in another domain. To cater for this we use "language extensions".

In the Spoofax ecosystem (in which IceDust is built), there are two ways to do language extension:

1. include the source of the parent language through maven artifacts
2. old fashioned Git forks

Using the Spoofax/Maven mechanism for language extensions currently has a couple of limitations, see http://yellowgrass.org/issue/Spoofax/211 .
Thus, at the moment we use old fashioned Git forks.
This means language extensions require some coordination with the IceDust development to ensure being able to pull upstream forks.

## Language extension process

1. Create a new repo, and push the IceDust/development branch to YourLanguage/icedust to be able to add extension points to IceDust or fix bugs in IceDust and pull request these.
2. Make a new development branch in which you develop your language

TODO: write a shell script that renames the language and changes the extension (without changing all paths of files).

## List of language extensions

* [IceDSL](https://github.com/MetaBorgCube/IceDSL): IceDust extension with WebDSL-specific features

