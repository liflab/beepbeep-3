BeepBeep 3: an expressive query processor for event streams
===========================================================

[![Build Status](https://semaphoreci.com/api/v1/projects/3743199c-0aa3-44d7-aac7-ee8219d22298/468154/badge.svg)](https://semaphoreci.com/sylvainhalle/beepbeep-3)

More to come.

Compiling and Installing BeepBeep 3                             {#install}
-----------------------------------

First make sure you have the following installed:

- The Java Development Kit (JDK) to compile. BeepBeep was developed and
  tested on version 7 of the JDK, but it is probably safe to use either
  version 6 or 8.
- [Ant](http://ant.apache.org) to automate the compilation and build process

Download the sources for BeepBeep from
[Bitbucket](http://bitbucket.org.com/sylvainhalle/cornipickle) or clone the
repository using Git:

    git@bitbucket.org:sylvainhalle/beepbeep-3.git

### Installing dependencies

The project requires the following libraries to be present in the system:

- The [Apache Commons CLI](http://commons.apache.org/proper/commons-cli/)
  to handle command-line parameters *(tested with version 1.3.1)*
- The [Bullwinkle parser](https://github.com/sylvainhalle/Bullwinkle),
  an on-the-fly parser for BNF grammars *(tested with version 1.1.5)*
  
Using Ant, you can automatically download any libraries missing from your
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

This will produce a file called `beepbeep3.jar` in the folder. This file
is runnable and stand-alone, or can be used as a library, so it can be moved
around to the location of your choice.

In addition, the script generates in the `doc` folder the Javadoc
documentation for using BeepBeep. This documentation is also embedded in
the JAR file. To show documentation in Eclipse, right-click on the jar,
click "Properties", then fill the Javadoc location (which is the JAR
itself).

### Testing

BeepBeep can test itself by running:

    ant test

Unit tests are run with [jUnit](http://junit.org); a detailed report of
these tests in HTML format is availble in the folder `tests/junit`, which
is automatically created. Code coverage is also computed with
[JaCoCo](http://www.eclemma.org/jacoco/); a detailed report is available
in the folder `tests/coverage`.

Command-line Usage                                                   {#cli}
------------------

Cornipickle works as an interactive interpreter. You start it on the
command line with:

    java -jar beepbeep3.jar

(More to come on command-line options.)

About the author                                                   {#about}
----------------

BeepBeep 3 was written by Sylvain Hallé, associate professor at Université
du Québec à Chicoutimi, Canada.
