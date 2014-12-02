// Copyright (c) 2014 K Team. All Rights Reserved.

net.virtualvoid.sbt.graph.Plugin.graphSettings

libraryDependencies ++= Seq(
  "org.scalacheck" %% "scalacheck" % "1.11.4" % "test",
  "com.novocode" % "junit-interface" % "0.9" % "test",
   "junit" % "junit" % "4.11" % "test"
)

EclipseKeys.withSource := true
