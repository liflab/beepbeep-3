#! /bin/bash
javafiles=$(find . -name "*.java")
for javafile in $javafiles
do
  echo -n "$javafile "
  git whatadded -- $javafile | grep "Date"
done
