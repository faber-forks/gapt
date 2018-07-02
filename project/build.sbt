resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.17"

addSbtPlugin( "org.scoverage" %% "sbt-scoverage" % "1.5.1" )

// Provides an assembly task which produces a fat jar with all dependencies included.
addSbtPlugin( "com.eed3si9n" % "sbt-assembly" % "0.14.6" )

addSbtPlugin( "com.eed3si9n" % "sbt-unidoc" % "0.4.1" )

addSbtPlugin( "org.scalariform" % "sbt-scalariform" % "1.8.2" )

addSbtPlugin( "org.foundweekends" % "sbt-bintray" % "0.5.4" )
