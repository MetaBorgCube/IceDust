# Relational programming

This is a programming language for relational programming; a declarative programming style based on modelling with first class relations.

## Getting the Editor - Java backend only

1. Get Spoofax from http://buildfarm.metaborg.org/job/spoofax-master/lastSuccessfulBuild/artifact/dist/
2. Check out this git repo
3. Build the editor project in [relations](relations)

## Getting the Editor - Java and WebDSL backend

1. Download any Eclipse
2. Install WebDSL through the update site http://webdsl.org/update/nightly
3. Check out this git repo
4. Build the editor project in [relations](relations)

<!--
## Getting the editor (install as Eclipse Plugin) - Has bugs

1. Get Eclipse 4.4
2. Install the new Relations Editor Plugin. Updatelink:  [http://dl.bintray.com/dcharkes/Relations-Language](http://dl.bintray.com/dcharkes/Relations-Language)

Note that there is an issue with the pre-packaged plugin. There is no command line output displayed ([Issue](http://yellowgrass.org/issue/StrategoXT/899)).
-->

## Try the examples

1. Check out this git repo
2. See the [relations-examples](relations-examples)

### Java backend

Compiling to Java will work always.

### WebDSL backend

Compiling to WebDSL requires you to have the Relations file the same name as the project name (case sensitive) and to be in the root folder of the project:

```
Demo (project name)
Demo/Demo.rel (relations file)
Demo/Demo.app (generated WebDSL file)
```

And `Demo.rel`:

```
module Demo

model

  //...
```
 
## Language Documentation

Currently the [relations-examples](relations-examples) are the documentation.
