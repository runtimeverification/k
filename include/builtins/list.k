// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "k-equal.k"
require "int.k"


module LIST
  imports K-EQUAL-HOOKS
  imports INT-HOOKS

  /*@ \section{Description} \K lists are ordered collections that may contain
   duplicate elements. These behave more like lists in functional programming
   languages than arrays in imperative programming languages; there's no
   numerical indexing, but instead specific elements are refered to using the
   Mylist,Mylist construct in combination with the MyListItem construct. It's 
   worth noting that \K lists aren't exactly like lists in functional languages;
   they're associative, which means that it's easy to access elements at both
   ends of the lists and concatenate them. For example, L:Mylist,E accesses
   element E at the end of a list. */

  /*@ \section{User-Defined Lists} It is very common in \K to define a shorthand
   for lists of user-defined sorts. \K 's builtin way of doing this is to use
   List\{K,"Separator"\}, where "Separator" is any valid character or sequence of
   characters used to separate distinct elements.
   For example, after defining \\
   syntax K ::= Elt\\ 
   a user could then define
   syntax Elts ::= List\{Elt,","\} \\
   which would be a comma-separated list whose elements are all of sort Elt. A
   user could just as well define \\
   syntax Elts ::= List\{Elt,"and"\} \\
   which would be a list containing elements of sort Elt that are separated with
   the word "and". If only one argument is given, the separator is asumed to be
   commas. So, \\
   syntax Elts = List\{Elt\} \\
   would define a comma-separated list containing elements of sort Elt.
  */


  /*@ Construct a List using two Lists. This is similar to the "Cons" operation
   in many functional programming languages.*/
  syntax List ::= List List   [left, function, hook(List:__), klabel('_List_)]
  /*@ Construct an empty list: */
  syntax List ::= ".List"       [function, hook(List:.List)]
  /*@ TODO: How does this work, exactly? Create a list with one element? Also,
   mention that MyListElement is commonly etended to create lists of arbitrary
   contents, especially tuples. */
  syntax List ::= ListItem(K)   [function, hook(List:ListItem)]

  /*@ Test element membership in the given list: */
  syntax Bool ::= K "in" List   [function]
//  rule
//    K1:K in /* L1:List */ ListItem(K2:K) L2:List
//  =>
//    K1 =K K2 orBool /* K1 in L1 orBool */ K1 in L2
//  rule _ in .List => false

  /*@  Get list length: */
  syntax Int ::= size(List)   [function, hook(Collection:size)]
//  rule
//    size(/* L1:List */ ListItem(_) L2:List)
//  =>
//    1 +Int /* size(L1) +Int */ size(L2)
//  rule size(.List) => 0
endmodule

