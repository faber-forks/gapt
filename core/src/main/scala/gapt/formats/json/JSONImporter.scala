package gapt.formats.json

import gapt.formats.InputFile
import io.circe.{ Decoder, Json }
import io.circe.parser._

object JSONImporter {
  /**
   * Imports a value for which a Decoder exists from JSON.
   */
  def apply[A]( file: InputFile )( implicit ev: Decoder[A] ): A = {
    val json: Json = parse( file.read ) match {
      case Left( f )  => throw new IllegalArgumentException( f.message )
      case Right( j ) => j
    }
    ev.decodeJson( json ) match {
      case Left( f )  => throw new IllegalArgumentException( f.message )
      case Right( x ) => x
    }
  }
}