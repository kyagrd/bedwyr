#!/usr/bin/perl

$side = "right" ;
$content = "" ;
# Trying to detect two consecutive printings of (left ...),
# ignoring (left ...) following by (right ...).
# This is slightly annoying to do because the trace (...) is pretty-printed
# on multiple lines.
while (<>) {
  if (/^\(([a-z]+)\s+(.*)$/) {
    $side = $1 ;
    if ($side eq "right") {
      $content = "" ;
    } else {
      if ($content ne "") {
        chop $content ;
        print
          "The following trace is not doable on the right:\n      $content\n" ;
        exit 0 ;
      }
      $content = $2 ;
    }
  } else {
    $content .= $_ ;
  }
}
