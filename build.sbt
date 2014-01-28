name := "project-euler"

version := "0.0.1"

organization := "dhe32.com"

scalaVersion := "2.10.3"

scalacOptions ++= Seq("-unchecked", "-feature", "-deprecation")

libraryDependencies ++= Seq(
"org.scalaj" % "scalaj-time_2.10.2" % "0.7", 
"org.scalaz" %% "scalaz-core" % "7.0.4", 
"org.spire-math" %% "spire" % "0.7.1", 
"org.apfloat" % "apfloat" % "1.7.1"
 )
