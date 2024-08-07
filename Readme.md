BeepBeep 3: an expressive query processor for event streams
===========================================================

[![Java CI](https://github.com/liflab/beepbeep-3/actions/workflows/ant-push.yml/badge.svg)](https://github.com/liflab/beepbeep-3/actions/workflows/ant-push.yml)
[![Coverity Scan Build Status](https://img.shields.io/coverity/scan/15149.svg?style=flat-square)](https://scan.coverity.com/projects/liflab-beepbeep-3)
[![Coverage](https://sonarcloud.io/api/project_badges/measure?project=liflab_beepbeep-3&metric=coverage)](https://sonarcloud.io/summary/new_code?id=liflab_beepbeep-3)
<img src="http://leduotang.ca/beepbeep-3.svg" height="20" alt="Downloads"/>

BeepBeep is an event stream query engine. It can take as input various
sources of *events*, pipe them through various *processors*, and produce
various kinds of output streams from them. For more information about
what is BeepBeep (including documentation, examples, etc.), please visit
[BeepBeep's website](http://liflab.github.io/beepbeep-3).

Using BeepBeep in a project
---------------------------

You can [download the latest JAR file](https://github.com/liflab/beepbeep-3/releases/latest)
and place it in your classpath. Otherwise, you can declare BeepBeep as a
dependency in your project.

### Maven

```xml
<dependency>
  <groupId>io.github.liflab</groupId>
  <artifactId>beepbeep-3</artifactId>
  <version>0.11.2</version>
</dependency>
```

### Ivy

```xml
<dependency org="io.github.liflab" name="beepbeep-3" rev="0.11.2"/>
```

### Gradle

```
compileOnly group: 'io.github.liflab', name: 'beepbeep-3', version: '0.11.2'
```

### Groovy

```
@Grab('io.github.liflab:beepbeep-3:0.11.2')
```

Repository structure
--------------------

The repository is separated across the following folders.

- `Core`: main source files
- `CoreTest`: test source files. You need to compile these files only
  if you want to run BeepBeep's unit tests.

Compiling the project contained in the present repository generates the
file `beepbeep-3.jar`, which is the minimal file you need to run BeepBeep on
your system.

### Extensions

BeepBeep's engine contains very few processors. In typical use cases,
these basic functionalities are extended by using one or more extra
*palettes*, such as those found in the
[BeepBeep palette repository](https://github.com/liflab/beepbeep-3-palettes).

Compiling and Installing BeepBeep 3
-----------------------------------

First make sure you have the following installed:

- The Java Development Kit (JDK) to compile. BeepBeep is developed to comply
  with Java version 8; it is probably safe to use any later version.
- [Ant](http://ant.apache.org) to automate the compilation and build process

Although the project contains a file named `pom.xml`, it does not contain
enough information to build from the sources (it only declares the project's
name and dependencies). You must use Ant.

Download the sources for BeepBeep from
[GitHub](https://github.com/liflab/beepbeep-3) or clone the
repository using Git:

    git@github.com:liflab/beepbeep-3.git

The repository is separated into multiple *projects*. Each of these
projects has the same Ant build script that allows you to compile them
(see below).

If the project you want to compile has dependencies,
 you can automatically download any libraries missing from your
system by typing:

    ant download-deps

This will put the missing JAR files in the `dep` folder in the project's
root.

### Compiling

Compile the sources by simply typing:

    ant

This will produce a file called `beepbeep-3-xxx.jar` (where `xxx` is
the version number) in the folder. This file is runnable and stand-alone,
or can be used as a library, so it can be moved around to the location of your
choice.

In addition, the script generates in the `doc` folder the Javadoc
documentation for using BeepBeep. To show documentation in Eclipse,
right-click on the jar, click "Properties", then fill the Javadoc location.

### Testing

BeepBeep can test itself by running:

    ant test

Unit tests are run with [jUnit](http://junit.org). By running:

    ant report

afterwards, a detailed report of these tests in HTML format is availble in the
folder `tests/junit`. Code coverage is also computed with
[JaCoCo](http://www.eclemma.org/jacoco/); a detailed report is available
in the folder `tests/coverage`.

### Coverity Scan

BeepBeep uses [Coverity Scan](https://scan.coverity.com) for static analysis
of its source code and defect detection. Instructions for using Coverity Scan
locally are detailed [here](https://scan.coverity.com/download?tab=java). In
a nutshell, if Coverity Scan is installed, type the following:

    cov-build --dir cov-int ant compile

(Make sure to clean up the directory first by launching `ant clean`, followed
by `ant download-deps`.)

Developing BeepBeep using Eclipse
---------------------------------

If you are using Eclipse to develop with BeepBeep, please refer to
the dedicated tutorial [Installing and Configuring in
Eclipse](https://docs.google.com/document/d/1o8dPn-1eEWmOzwdeAr_7eqa88iKrYmL63-rGtkloU6k/edit?usp=sharing),
written by Jalves Nicacio.

In short:

- Create a new empty workspace (preferably in a new, empty folder).
- Create new projects for each of the folders `Core`,
  `CoreTest`, and optionally, any of the palette folders you with to develop.
  Note that these projects will not be located in the
  default location with respect to the workspace; you need to uncheck
  the "Use default location" option and fetch them manually.
  
Then, setup the build path for each project:

- `Core` requires the Bullwinkle library (see above)
- `CoreTest` depends on `Core` and requires the JUnit *4* library
- Each of the palette folders depend on `Core` and require the JUnit
  *4* library
- In addition, some of the palette projects may have other
  dependencies; please refer to their individual documentation

Warning
-------

The BeepBeep project is under heavy development. The repository may be
restructured, the API may change, and so on. This is R&D!

About the author
----------------

BeepBeep 3 was written by [Sylvain Hallé](https://leduotang.ca/sylvain),
full professor at Université du Québec à Chicoutimi, Canada. Part of
this work has been funded by the Canada Research Chair in Software
Specification, Testing and Verification and the
[Natural Sciences and Engineering Research Council
of Canada](http://nserc-crsng.gc.ca).
