// See README.md for license details.

ThisBuild / scalaVersion := "2.12.15"
ThisBuild / version      := "0.1.0"
ThisBuild / organization := "liuyic00"

val chiselVersion = "3.5.4"

lazy val root = (project in file("."))
  .settings(
    name := "kcpu",
    libraryDependencies ++= Seq(
      "edu.berkeley.cs" %% "chisel3"    % chiselVersion,
      "edu.berkeley.cs" %% "chiseltest" % "0.5.4" % "test"
    ),
    scalacOptions ++= Seq(
      "-Xsource:2.11",
      "-language:reflectiveCalls",
      "-deprecation",
      "-feature",
      "-Xcheckinit"
    ),
    addCompilerPlugin(
      "edu.berkeley.cs" % "chisel3-plugin" % chiselVersion cross CrossVersion.full
    )
  )
