resolvers += Classpaths.sbtPluginReleases
logLevel := Level.Warn

libraryDependencies += "org.apache.commons" % "commons-compress" % "1.10"

addSbtPlugin( "org.scoverage" %% "sbt-scoverage" % "1.3.3" )
addSbtPlugin( "org.scoverage" % "sbt-coveralls" % "1.0.3" )

// Provides an assembly task which produces a fat jar with all dependencies included.
addSbtPlugin( "com.eed3si9n" % "sbt-assembly" % "0.14.1" )

addSbtPlugin( "org.scalariform" % "sbt-scalariform" % "1.5.1" )

addSbtPlugin( "me.lessis" % "bintray-sbt" % "0.3.0" )
