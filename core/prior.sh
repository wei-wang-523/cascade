#! /bin/sh

java -cp ${project.build.dependencies}:core-0.0.1-SNAPSHOT.jar edu.nyu.cascade.SPL $*
