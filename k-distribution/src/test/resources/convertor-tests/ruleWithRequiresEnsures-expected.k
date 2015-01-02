// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(9),endColumn(9))]
  syntax Exp [location(startLine(4),startColumn(3),endLine(4),endColumn(12))]
  rule A [location(startLine(8),startColumn(8),endLine(8),endColumn(13)) sort(Exp)]=>A [location(startLine(8),startColumn(17),endLine(8),endColumn(18)) sort(Exp)] requires A [location(startLine(8),startColumn(28),endLine(8),endColumn(29)) sort(Exp)] ensures A [location(startLine(8),startColumn(38),endLine(8),endColumn(39)) sort(Exp)] [location(startLine(8),startColumn(3),endLine(8),endColumn(38))]
  rule A [location(startLine(7),startColumn(8),endLine(7),endColumn(13)) sort(Exp)]=>A [location(startLine(7),startColumn(17),endLine(7),endColumn(18)) sort(Exp)] requires true ensures A [location(startLine(7),startColumn(27),endLine(7),endColumn(28)) sort(Exp)] [location(startLine(7),startColumn(3),endLine(7),endColumn(27))]
  rule A [location(startLine(6),startColumn(8),endLine(6),endColumn(13)) sort(Exp)]=>A [location(startLine(6),startColumn(17),endLine(6),endColumn(18)) sort(Exp)] requires A [location(startLine(6),startColumn(28),endLine(6),endColumn(29)) sort(Exp)] ensures true [location(startLine(6),startColumn(3),endLine(6),endColumn(28))]
endmodule
