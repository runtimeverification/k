red #mul( #NaN, #NaN )						==Bool		#NaN .
red #mul( #NaN, #n(123) )					==Bool		#NaN .
red #mul( #n(-123), #NaN, )					==Bool		#NaN .
red #div( #NaN, #NaN )						==Bool		#NaN .
red #div( #NaN, #n(123) )					==Bool		#NaN .
red #div( #n(-123), #NaN, )					==Bool		#NaN .


red #div( #n(0), #infinity(1) )				==Bool		#n(0) .
red #div( #n(123), #infinity(1) )			==Bool		#n(0) .
red #div( #n(-123), #infinity(1) )			==Bool		#n(-0.0) .
red #div( #n(123), #infinity(-1) )			==Bool		#n(-0.0) .

red #div( #infinity(1), #n(0) )				==Bool		#(infinity(1)) .
red #div( #infinity(-1), #n(0) )			==Bool		#(infinity(-1)) .
red #div( #infinity(1), #n(-0.0) )			==Bool		#(infinity(-1)) .
red #div( #infinity(1), #n(123) )			==Bool		#(infinity(1)) .
red #div( #infinity(1), #n(-123) )			==Bool		#(infinity(-1)) .

red #div( #infinity(1), #infinity(1) )		==Bool		#NaN .
red #div( #infinity(-1), #infinity(1) )		==Bool		#NaN .

red #mul( #n(0), #infinity(1) )				==Bool		#NaN .
red #mul( #infinity(-1), #n(0) )			==Bool		#NaN .

red #mul( #n(123), #infinity(1) )			==Bool		#(infinity(1)) .
red #mul( #infinity(1), #n(-123) )			==Bool		#(infinity(-1)) .


red #mul( #infinity(1), #infinity(1) )		==Bool		#infinity(1) .
red #mul( #infinity(-1), #infinity(1) )		==Bool		#infinity(-1) .
red #mul( #infinity(-1), #infinity(-1) )	==Bool		#infinity(1) .

red #add( #infinity(1), #infinity(1) )		==Bool		#infinity(1) .
red #add( #infinity(-1), #infinity(1) )		==Bool		#NaN .
red #add( #infinity(-1), #infinity(-1) )	==Bool		#infinity(-1) .

red #sub( #infinity(1), #infinity(1) )		==Bool		#NaN .
red #sub( #infinity(-1), #infinity(1) )		==Bool		#infinity(-1) .
red #add( #infinity(-1), #infinity(-1) )	==Bool		#infinity(-1) .


red #div( #n(0), #n(0) )					==Bool		#NaN .
red #div( #n(0), #n(-0.0) )					==Bool		#NaN .
red #div( #n(0), #n(1) )					==Bool		#n(0) .
red #div( #n(0), #n(-123) )					==Bool		#n(0) .

red #div( #n(0), #n(0) )					==Bool		#NaN .
red #div( #n(-123), #n(0) )					==Bool		#infinity(-1) .
red #div( #n(123), #n(0) )					==Bool		#infinity(1) .
red #div( #n(123), #n(-0.0) )				==Bool		#infinity(-1) .
red #div( #n(123), #n(0) )					==Bool		#infinity(1) .


red #identical( #(0), #(-0.0))		==Bool	#(true)
