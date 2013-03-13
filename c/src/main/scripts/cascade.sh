#! /bin/sh

Z3_LIB_DIR="${z3.libdir}"
Z3_JAR="${z3.jar}"
CASCADE_BIN_DIR="${project.build.directory}"
CASCADE_JAR="$CASCADE_BIN_DIR/${project.build.finalName}-jar-with-dependencies.jar"

DYLD_LIBRARY_PATH=$Z3_LIB_DIR:$DYLD_LIBRARY_PATH

java -ea -cp "$Z3_JAR:$CASCADE_JAR" edu.nyu.cascade.c.Main "$@"
