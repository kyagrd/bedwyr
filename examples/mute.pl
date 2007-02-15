#!/usr/bin/perl

$left = "" ;
while (<>) {
  if (/^\(left\s+(.*)\)$/) {
    if ("" eq $left) {
      $left = $1 ;
    } else {
      print "The following trace is not doable on the right:\n$left\n" ;
      exit 0 ;
    }
  } else {
    $left = "" ;
  }
}
