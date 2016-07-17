BeepBeep 3: an expressive query processor for event streams
===========================================================

[![Build Status](https://semaphoreci.com/api/v1/projects/3743199c-0aa3-44d7-aac7-ee8219d22298/468154/badge.svg)](https://semaphoreci.com/sylvainhalle/beepbeep-3)

BeepBeep is an event stream query engine. It can take as input various
sources of *events*, pipe them through various *processors*, and produce
various kinds of output streams from them. For more information about
what is BeepBeep (including documentation, examples, etc.), please visit
[BeepBeep's website](http://liflab.github.io/beepbeep-3).

Repository structure                                           {#structure}
--------------------

The repository is separated across the following folders.

### Engine

`Engine` contains the source files for BeepBeep's core. It is separated in
two projects:

- `Core`: main source files
- `CoreTest`: test source files. You need to compile these files only
  if you want to run BeepBeep's unit tests.

Compiling the project contained in that folder generates the file
`beepbeep-3.jar`, which is the minimal file you need to run BeepBeep on
your system.

BeepBeep tries to have as few dependencies as possible. However, the
following companion library needs to be installed for BeepBeep to
compile and run:

- The [Bullwinkle parser](https://github.com/sylvainhalle/Bullwinkle),
  an on-the-fly parser for BNF grammars *(tested with version 1.2)*

### Extensions

`Extensions` contains a number of projects producing various independent
extensions to BeepBeep. Each project is also independent from the others, and
can be built separately. All projects require `beepbeep-3.jar` in their
classpath (or alternately, must point to the `Core` source files) in order to
compile and run.

At the moment, the folder contains the following extensions:

- `Gnuplot`: for drawing plots from event streams
- `Jdbc`: for using BeepBeep as a JDBC driver
- `Json`: to read and write events in the JSON format
- `Ltl`: to express properties in Linear Temporal Logic
- `Sets`: to manipulate streams of sets
- `Signal`: basic signal processing functions (peak detection, etc.)
- `WebSocket`: to read/write events from/to a web socket
- `Xml`: to read and write events in the JSON format

Depending on the projects, additional dependencies may need to be
downloaded and installed. Please refer to the `Readme.md` file of each
particular project (if any) for more information on compiling and
building these extensions.

### Editor

`Editor` is a web-based graphical editor to create chains of BeepBeep
processors. This project is under heavy construction (in other words, it
doesn't work yet), and at the moment is far less mature than the engine
and its extensions.

Compiling and Installing BeepBeep 3                              {#install}
-----------------------------------

First make sure you have the following installed:

- The Java Development Kit (JDK) to compile. BeepBeep was developed and
  tested on version 7 of the JDK, but it is probably safe to use either
  version 6 or 8.
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
documentation for using BeepBeep. This documentation is also embedded in
the JAR file. To show documentation in Eclipse, right-click on the jar,
click "Properties", then fill the Javadoc location (which is the JAR
itself).

### Testing

Each project can test itself by running:

    ant test

Unit tests are run with [jUnit](http://junit.org); a detailed report of
these tests in HTML format is availble in the folder `tests/junit`, which
is automatically created. Code coverage is also computed with
[JaCoCo](http://www.eclemma.org/jacoco/); a detailed report is available
in the folder `tests/coverage`.

Developing BeepBeep using Eclipse                                {#eclipse}
---------------------------------

If you wish to develop BeepBeep, here is a suggested setup using Eclipse.

- Create a new empty workspace. You may use the root of the repository as
  the workspace's folder.
- Create new projects for each of the folders `Engine/Core`,
  `Engine/CoreTest`, and optionally, any of the `Extensions/xxx` folders
  you with to develop. Note that these projects are not located in the
  default location with respect to the workspace; you need to uncheck
  the "Use default location" option and fetch their folder manually.
  
Then, setup the build path for each project:

- `Engine/Core` requires the Bullwinkle library (see above)
- `Engine/CoreTest` depends on `Core` and requires the JUnit 4 library
- Each of the `Extensions/xxx` depend on `Core` and require the JUnit
  4 library
- In addition, some of the `Extensions` projects may have other
  dependencies; please refer to their individual documentation

Warning                                                          {#warning}
-------

The BeepBeep project is under heavy development. The repository may be
restructured, the API may change, and so on. This is R&D!

About the author                                                   {#about}
----------------

BeepBeep 3 was written by Sylvain Hallé, associate professor at Université
du Québec à Chicoutimi, Canada.
