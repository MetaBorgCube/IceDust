# Relational programming

This is a programming language for relational programming; a declarative programming style based on modelling with first class relations.

## Getting the Editor

Download from http://buildfarm.metaborg.org/job/relations-eclipsegen/

Known issues:

* Generation > Execute Java does not show any output on the console (Generation > Generate Java and then running the Java program from Eclipse works fine)
* The WebDSL editor fails to analyze its files when the Relation Language Editor is also installed (building the generated WebDSL files works fine)

## Building the Editor (in Spoofax)

1. Get Spoofax from http://buildfarm.metaborg.org/job/spoofax-master/lastSuccessfulBuild/artifact/dist/ (Only Java backend)
   Or get WebDSL+Spoofax from http://buildfarm.metaborg.org/job/webdsl-eclipsegen/ (Works for both Java and WebDSL backend)
2. Check out this git repo
3. Build the editor project in [relations](relations)

Building the editor in Spoofax does not have both issues listed for the Download.


## Try the examples

1. Check out this git repo
2. See the [relations-examples](relations-examples)

### Java backend

To use the Java backend use Generation > Execute Java (if you built the editor in Spoofax).

Or use Generation > Generate Java and build the generated Java (make sure the Java files are on the classpath and that your eclipse project has the Java nature and Java builder) (if you have downloaded the editor).

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

2. Use `Generation > Generate WebDSL eager` to generate the `.app` file.
3. And then right click the project `Convert to a WebDSL project`.
4. Press `Cmd + Alt + B` in the `.app` file to trigger the WebDSL compiler.
 
## Language Documentation

Currently the [relations-examples](relations-examples) are the documentation.
