#! /bin/sh

Z3_LIB_DIR="${z3.libdir}"
Z3_JAR="${z3.jar}"
CVC4_LIB_DIR="${cvc4.libdir}"
CVC4_JNI_LIB_DIR="${cvc4.jni.libdir}"
CVC4_JAR="${cvc4.jar}"

CASCADE_BIN_DIR="${project.build.directory}"
CASCADE_JAR="$CASCADE_BIN_DIR/${project.build.finalName}-jar-with-dependencies.jar"

export DYLD_LIBRARY_PATH=$Z3_LIB_DIR:$CVC4_LIB_DIR:$CVC4_JNI_LIB_DIR:$DYLD_LIBRARY_PATH
export LD_LIBRARY_PATH=$Z3_LIB_DIR:$CVC4_LIB_DIR:$CVC4_JNI_LIB_DIR:$LD_LIBRARY_PATH

java -ea -cp "$Z3_JAR:$CVC4_JAR:$CASCADE_JAR" edu.nyu.cascade.c.Main "$@"
