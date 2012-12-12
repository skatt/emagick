# Wrapper in Erlang for Image/GraphicsMagick

Simple wrapper for GraphicsMagick or ImageMagick using an Erlang port.


## Dependencies

Either GraphicsMagick or ImageMagick commandline tools are of course
required. On a Debian based system install either `graphicsmagick` or
`imagemagick` and then configure `magick_command` in `emagick.app.src`
accordingly.

The Erlang package erlang-uuid is another dependency

    http://gitorious.org/avtobiff/erlang-uuid.git


## Installation

Build and install with the supplied Makefile or use rebar. Simply typing
`make` will build emagick.


## Configuration

It is possible to choose what \*magick command to run and what path to
use as working directory (default `/tmp/emagick`). These setting are in
`emagick.app.src`.


## Example usage

    1> application:start(emagick).
    2> {ok, Pdf} = file:read_file("something.pdf").
    3> {ok, Png} = emagick:convert(PDF, pdf, png, [{density, [200]}]).
    4> ok = file:write_file("something.png", Png).


## License

emagick is released under an MIT license. See LICENSE for the full
license text.


 vim:ft=markdown:tw=72