BeepBeep 3: an expressive query processor for event streams
===========================================================

[![Travis](https://img.shields.io/travis/liflab/beepbeep-3.svg?style=flat-square)]()
[![SonarQube Coverage](https://img.shields.io/sonar/http/sonarqube.com/liflab:beepbeep-3/coverage.svg?style=flat-square)]()

BeepBeep is an event stream query engine. It can take as input various
sources of *events*, pipe them through various *processors*, and produce
various kinds of output streams from them. For more information about
what is BeepBeep (including documentation, examples, etc.), please visit
[BeepBeep's website](http://liflab.github.io/beepbeep-3).

Repository structure                                           {#structure}
--------------------

The repository is separated across the following folders.

- `Core`: main source files
- `CoreTest`: test source files. You need to compile these files only
  if you want to run BeepBeep's unit tests.

Compiling the project contained in the present repository generates the
file `beepbeep-3.jar`, which is the minimal file you need to run BeepBeep on
your system.

BeepBeep tries to have as few dependencies as possible. However, the
following companion library needs to be installed for BeepBeep to
compile and run:

- The [Bullwinkle parser](https://github.com/sylvainhalle/Bullwinkle),
  an on-the-fly parser for BNF grammars *(tested with version 1.3.1)*

### Extensions

BeepBeep's engine contains very few processors. In typical use cases,
these basic functionalities are extended by using one or more extra
*palettes*, such as those found in the
[BeepBeep palette repository](https://github.com/liflab/beepbeep-3-palettes).

Compiling and Installing BeepBeep 3                              {#install}
-----------------------------------

First make sure you have the following installed:

- The Java Development Kit (JDK) to compile. BeepBeep is developed to comply
  with Java version 6; it is probably safe to use any later version.
- [Ant](http://ant.apache.org) to automate the compilation and build process

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

This will put the missing JAR files in the `deps` folder in the project's
root. These libraries should then be put somewhere in the classpath, such as
in Java's extension folder (don't leave them there, it won't work). You can
do that by typing (**with administrator rights**):

    ant install-deps

or by putting them manually in the extension folder. Type `ant init` and it
will print out what that folder is for your system.

Do **not** create subfolders there (i.e. put the archive directly in that
folder).

### Compiling

Compile the sources by simply typing:

    ant

This will produce a file called `beepbeep-3.jar` (or another library,
depending on what you are compiling) in the folder. This file
is runnable and stand-alone, or can be used as a library, so it can be moved
around to the location of your choice.

In addition, the script generates in the `doc` folder the Javadoc
documentation for using BeepBeep. To show documentation in Eclipse,
right-click on the jar, click "Properties", then fill the Javadoc location.

### Testing

BeepBeep can test itself by running:

    ant test

Unit tests are run with [jUnit](http://junit.org); a detailed report of
these tests in HTML format is availble in the folder `tests/junit`, which
is automatically created. Code coverage is also computed with
[JaCoCo](http://www.eclemma.org/jacoco/); a detailed report is available
in the folder `tests/coverage`.

Developing BeepBeep using Eclipse                                {#eclipse}
---------------------------------

If you wish to develop BeepBeep in Eclipse, please follow the
[detailed instructions](https://liflab.github.io/beepbeep-3/guide/building-eclipse.html)
(with screenshots and all) found in the online user guide.

In short:

- Create a new empty workspace (preferably in a new, empty folder).
- Create new projects for each of the folders `Core`,
  `CoreTest`, and optionally, any of the palette folders you with to develop.
  Note that these projects will not be located in the
  default location with respect to the workspace; you need to uncheck
  the "Use default location" option and fetch them manually.
  
Then, setup the build path for each project:

- `Core` requires the Bullwinkle library (see above)
- `CoreTest` depends on `Core` and requires the JUnit 4 library
- Each of the palette folders depend on `Core` and require the JUnit
  4 library
- In addition, some of the palette projects may have other
  dependencies; please refer to their individual documentation

Warning                                                          {#warning}
-------

The BeepBeep project is under heavy development. The repository may be
restructured, the API may change, and so on. This is R&D!

About the author                                                   {#about}
----------------

BeepBeep 3 was written by [Sylvain Hallé](http://leduotang.ca/sylvain),
associate professor at Université du Québec à Chicoutimi, Canada. Part of
this work has been funded by the Canada Research Chair in Software
Specification, Testing and Verification and the
[Natural Sciences and Engineering Research Council
of Canada](http://nserc-crsng.gc.ca).
