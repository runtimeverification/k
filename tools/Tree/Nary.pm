#####################################################################################
# $Id: Nary.pm,v 1.3 2004/01/05 10:32:00 soriano Exp $
#####################################################################################
#
# Tree::Nary
#
# Author: Frederic Soriano <frederic.soriano@alcatel.fr>
# RCS Revision: $Revision: 1.3 $
# Date: $Date: 2004/01/05 10:32:00 $
#
#####################################################################################
#
# This package is free software and is provided "as is" without express or
# implied warranty.  It may be used, redistributed and/or modified under the
# same terms as Perl itself.
#
#####################################################################################

package Tree::Nary;

require 5.003;
require Exporter;

@ISA = qw(Exporter);

$VERSION = '1.3';

use strict;
use vars qw($TRUE $FALSE);
use vars qw($TRAVERSE_LEAFS $TRAVERSE_NON_LEAFS $TRAVERSE_ALL $TRAVERSE_MASK);
use vars qw($IN_ORDER $PRE_ORDER $POST_ORDER $LEVEL_ORDER);

#
# Constants
#

# Booleans
*TRUE  = \1;
*FALSE = \0;

# Tree traverse flags
*TRAVERSE_LEAFS		= \(1 << 0);					# Only leaf nodes should be visited.
*TRAVERSE_NON_LEAFS	= \(1 << 1);					# Only non-leaf nodes should be visited.
*TRAVERSE_ALL		= \($TRAVERSE_LEAFS | $TRAVERSE_NON_LEAFS);	# All nodes should be visited.
*TRAVERSE_MASK		= \0x03;

# Tree traverse orders
*IN_ORDER		= \1;
*PRE_ORDER		= \2;
*POST_ORDER		= \3;
*LEVEL_ORDER		= \4;

#
# Public methods
#

# Constructors, destructors

# Creates a new Tree::Nary node object, containing the given data, if any.
# Used to create the first node in a tree.
sub new() {

	my ($that, $newdata) = (shift, shift);
	my $class = ref($that) || $that;
	my $self = {
		data		=> undef,
		next		=> undef,
		prev		=> undef,
		parent		=> undef,
		children	=> undef,
	};

	if(defined($newdata)) {
		$self->{data} = $newdata;
	}

	# Transform $self into an object of class $class
	bless $self, $class;

	return($self);
}

# Frees allocated memory by removing circular references.
sub _free() {

	my ($self, $node) = (shift, shift);
	my $parent = $self->new();

	$parent = $node;

	while($TRUE) {
		if(defined($parent->{children})) {
			$self->_free($parent->{children});
		}
		if(defined($parent->{next})) {
			$parent = $parent->{next};
		} else {
			last;
		}
	}

	return;
}

# Removes the node and its children from the tree.
sub DESTROY() {

	my ($self, $root) = (shift, shift);

	if(!defined($root)) {
		return;
	}
	if(!$self->is_root($root)) {
		$self->unlink($root);
	}

	$self->_free($root);

	return;
}

# Unlinks a node from a tree, resulting in two separate trees.
sub unlink() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return;
	}

	if(defined($node->{prev})) {
		$node->{prev}->{next} = $node->{next};
	} elsif(defined($node->{parent})) {
		$node->{parent}->{children} = $node->{next};
	}

	$node->{parent} = undef;

	if(defined($node->{next})) {
		$node->{next}->{prev} = $node->{prev};
		$node->{next} = undef;
	}

	$node->{prev} = undef;

	return;
}

#
# Miscellaneous info methods
#

# Returns TRUE if the given node is a root node.
sub is_root() {

	my ($self, $node) = (shift, shift);

	return(!defined($node->{parent}) && !defined($node->{prev}) && !defined($node->{next}));
}

# Returns TRUE if the given node is a leaf node.
sub is_leaf() {

	my ($self, $node) = (shift, shift);

	return(!defined($node->{children}));
}

# Returns TRUE if $node is an ancestor of $descendant.
# This is true if node is the parent of descendant, or if node is the grandparent of descendant, etc.
sub is_ancestor() {

	my ($self, $node, $descendant) = (shift, shift, shift);

	if(!defined($node)) {
		return($FALSE);
	}
	if(!defined($descendant)) {
		return($FALSE);
	}

	while(defined($descendant)) {
		if(defined($descendant->{parent}) && ($descendant->{parent} == $node)) {
			return($TRUE);
		}

		$descendant = $descendant->{parent};
	}

	return($FALSE);
}

# Gets the root of a tree.
sub get_root() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	while(defined($node->{parent})) {
		$node = $node->{parent};
	}

	return($node);
}

# Gets the depth of a node.
sub depth() {

	my ($self, $node) = (shift, shift);
	my $depth = 0;

	while(defined($node)) {
		$depth++;
		$node = $node->{parent};
	}

	return($depth);
}

# Reverses the order of the children of a node.
sub reverse_children() {

	my ($self, $node) = (shift, shift);
	my $child = $self->new();
	my $last = $self->new();

	if(!defined($node)) {
		return;
	}

	$child = $node->{children};

	while(defined($child)) {
		$last = $child;
		$child = $last->{next};
		$last->{next} = $last->{prev};
		$last->{prev} = $child;
	}

	$node->{children} = $last;

	return;
}

# Gets the maximum height of all branches beneath a node.
# This is the maximum distance from the node to all leaf nodes.
sub max_height() {

	my ($self, $root) = (shift, shift);
	my $child = $self->new();
	my $max_height = 0;

	# <Deep recursion on subroutine "Tree::Nary::max_height">
	#   can be safely ignored.
	local $^W = 0;

	if(!defined($root)) {
		return(0);
	}

	$child = $root->{children};

	while(defined($child)) {

		my $tmp_height = $self->max_height($child);

		if($tmp_height > $max_height) {
			$max_height = $tmp_height;
		}

		$child = $child->{next};
	}

	return($max_height + 1);
}

# Gets the number of children of a node.
sub n_children() {

	my ($self, $node) = (shift, shift);
	my $n = 0;

	if(!defined($node)) {
		return(0);
	}

	$node = $node->{children};

	while(defined($node)) {
		$n++;
		$node = $node->{next};
	}

	return($n);
}

# Gets the position of a node with respect to its siblings.
# $child must be a child of $node.
# The first child is numbered 0, the second 1, and so on.
sub child_position() {

	my ($self, $node, $child) = (shift, shift, shift);
	my $n = 0;

	if(!defined($node)) {
		return(-1);
	}
	if(!defined($child)) {
		return(-1);
	}
	if(defined($child->{parent}) && !($child->{parent} == $node)) {
		return(-1);
	}

	$node = $node->{children};

	while(defined($node)) {
		if($node == $child) {
			return($n);
		}
		$n++;
		$node = $node->{next};
	}

	return(-1);
}

# Gets the position of the first child of a node which contains the given data.
sub child_index() {

	my ($self, $node, $data) = (shift, shift, shift);
	my $n = 0;

	if(!defined($node)) {
		return(-1);
	}

	$node = $node->{children};

	while(defined($node)) {
		if($node->{data} eq $data) {
			return($n);
		}
		$n++;
		$node = $node->{next};
	}

	return(-1);
}

# Gets the first sibling of a node. This could possibly be the node itself.
sub first_sibling() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	while(defined($node->{prev})) {
		$node = $node->{prev};
	}

	return($node);
}

# Gets the next sibling of a node.
sub next_sibling() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	return($node->{next});
}

# Gets the previous sibling of a node.
sub prev_sibling() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	return($node->{prev});
}

# Gets the last sibling of a node. This could possibly be the node itself.
sub last_sibling() {

	my ($self, $node) = (shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	while(defined($node->{next})) {
		$node = $node->{next};
	}

	return($node);
}

sub _count_func() {

	my ($self, $node, $flags, $nref) = (shift, shift, shift, shift);

	# <Deep recursion on subroutine "Tree::Nary::_count_func"> warnings
	#   can be safely ignored.
	local $^W = 0;

	if(defined($node->{children})) {

		my $child = $self->new();

		if($flags & $TRAVERSE_NON_LEAFS) {
			$$nref++;
		}

		$child = $node->{children};

		while(defined($child)) {
			$self->_count_func($child, $flags, $nref);
			$child = $child->{next};
		}

	} elsif($flags & $TRAVERSE_LEAFS) {
		$$nref++;
	}

	return;
}

# Gets the number of nodes in a tree.
sub n_nodes() {

	my ($self, $root, $flags) = (shift, shift, shift);
	my $n = 0;

	if(!(defined($root))) {
		return(0);
	}
	if(!($flags <= $TRAVERSE_MASK)) {
		return(0);
	}

	$self->_count_func($root, $flags, \$n);

	return($n);
}

# Gets the first child of a node.
sub first_child() {

	my ($self, $node) = (shift, shift);

	if(!(defined($node))) {
		return(undef);
	}

	return($node->{children});
}

# Gets the last child of a node.
sub last_child() {

	my ($self, $node) = (shift, shift);

	if(!(defined($node))) {
		return(undef);
	}

	$node = $node->{children};

	if(defined($node)) {
		while(defined($node->{next})) {
			$node = $node->{next};
		}
	}

	return($node);
}

# Gets a child of a node, using the given index.
# the first child is at index 0.
# If the index is too big, 'undef' is returned.
sub nth_child() {

	my ($self, $node, $n) = (shift, shift, shift);

	if(!defined($node)) {
		return(undef);
	}

	$node = $node->{children};

	if(defined($node)) {
		while(($n-- > 0) && defined($node)) {
			$node = $node->{next};
		}
	}

	return($node);
}

#
# Insert methods
#

# Inserts a node beneath the parent at the given position.
sub insert() {

	my ($self, $parent, $position, $node) = (shift, shift, shift, shift);

	if(!defined($parent)) {
		return($node);
	}
	if(!defined($node)) {
		return($node);
	}
	if(!$self->is_root($node)) {
		return($node);
	}

	if($position > 0) {
		return($self->insert_before($parent, $self->nth_child($parent, $position), $node));
	} elsif($position == 0) {
		return($self->prepend($parent, $node));
	} else {
		return($self->append($parent, $node));
	}
}

# Inserts a node beneath the parent before the given sibling.
sub insert_before() {

	my ($self, $parent, $sibling, $node) = (shift, shift, shift, shift);

	if(!defined($parent)) {
		return($node);
	}
	if(!defined($node)) {
		return($node);
	}
	if(!$self->is_root($node)) {
		return($node);
	}

	if(defined($sibling)) {
		if($sibling->{parent} != $parent) {
			return($node);
		}
	}

	$node->{parent} = $parent;

	if(defined($sibling)) {
		if(defined($sibling->{prev})) {
			$node->{prev} = $sibling->{prev};
			$node->{prev}->{next} = $node;
			$node->{next} = $sibling;
			$sibling->{prev} = $node;
		} else {
			$node->{parent}->{children} = $node;
			$node->{next} = $sibling;
			$sibling->{prev} = $node;
		}
	} else {
		if(defined($parent->{children})) {
			$sibling = $parent->{children};

			while(defined($sibling->{next})) {
				$sibling = $sibling->{next};
			}

			$node->{prev} = $sibling;
			$sibling->{next} = $node;
		} else {
			$node->{parent}->{children} = $node;
		}
	}

	return($node);
}

# Inserts a new node at the given position.
sub insert_data() {

	my ($self, $parent, $position, $data) = (shift, shift, shift, shift);

	return($self->insert($parent, $position, $self->new($data)));
}

# Inserts a new node before the given sibling.
sub insert_data_before() {

	my ($self, $parent, $sibling, $data) = (shift, shift, shift, shift);

	return($self->insert_before($parent, $sibling, $self->new($data)));
}

# Inserts a node as the last child of the given parent.
sub append() {

	my ($self, $parent, $node) = (shift, shift, shift);

	return($self->insert_before($parent, undef, $node));
}

# Inserts a new node as the first child of the given parent.
sub append_data() {

	my ($self, $parent, $data) = (shift, shift, shift);

	return($self->insert_before($parent, undef, $self->new($data)));
}

# Inserts a node as the first child of the given parent.
sub prepend() {

	my ($self, $parent, $node) = (shift, shift, shift);

	if(!defined($parent)) {
		return($node);
	}

	return($self->insert_before($parent, $parent->{children}, $node));
}

# Inserts a new node as the first child of the given parent.
sub prepend_data() {

	my ($self, $parent, $data) = (shift, shift, shift);

	return($self->prepend($parent, $self->new($data)));
}

#
# Search methods
#

sub _traverse_pre_order() {

	my ($self, $node, $flags, $funcref, $argref) = (shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		my $child = $self->new();

		if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

		$child = $node->{children};

		while(defined($child)) {

			my $current = $self->new();

			$current = $child;
			$child = $current->{next};
			if($self->_traverse_pre_order($current, $flags, $funcref, $argref)) {
				return($TRUE);
			}
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _depth_traverse_pre_order() {

	my ($self, $node, $flags, $depth, $funcref, $argref) = (shift, shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		my $child = $self->new();

		if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

		$depth--;
		if(!$depth) {
			return($FALSE);
		}

		$child = $node->{children};

		while(defined($child)) {

			my $current = $self->new();

			$current = $child;
			$child = $current->{next};

			if($self->_traverse_pre_order($current, $flags, $depth, $funcref, $argref)) {
				return($TRUE);
			}
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _traverse_post_order() {

	my ($self, $node, $flags, $funcref, $argref) = (shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		my $child = $self->new();

		$child = $node->{children};

		while(defined($child)) {

			my $current = $self->new();

			$current = $child;
			$child = $current->{next};

			if($self->_traverse_post_order($current, $flags, $funcref, $argref)) {
				return($TRUE);
			}
		}

		if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _depth_traverse_post_order() {

	my ($self, $node, $flags, $depth, $funcref, $argref) = (shift, shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		$depth--;
		if($depth) {

			my $child = $self->new();

			$child = $node->{children};

			while(defined($child)) {

				my $current = $self->new();

				$current = $child;
				$child = $current->{next};

				if($self->_depth_traverse_post_order($current, $flags, $depth, $funcref, $argref)) {
					return($TRUE);
				}
			}
		}
		if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _traverse_in_order() {

	my ($self, $node, $flags, $funcref, $argref) = (shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		my $child = $self->new();
		my $current = $self->new();

		$child = $node->{children};
		$current = $child;
		$child = $current->{next};

		if($self->_traverse_in_order($current, $flags, $funcref, $argref)) {
			return($TRUE);
		}
		if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

		while(defined($child)) {
			$current = $child;
			$child = $current->{next};
			if($self->_traverse_in_order($current, $flags, $funcref, $argref)) {
				return($TRUE);
			}
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _depth_traverse_in_order() {

	my ($self, $node, $flags, $depth, $funcref, $argref) = (shift, shift, shift, shift, shift, shift);

	if(defined($node->{children})) {

		$depth--;
		if($depth) {

			my $child = $self->new();
			my $current = $self->new();

			$child = $node->{children};
			$current = $child;
			$child = $current->{next};

			if($self->_depth_traverse_in_order($current, $flags, $depth, $funcref, $argref)) {
				return($TRUE);
			}
			if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
				return($TRUE);
			}

			while(defined($child)) {
				$current = $child;
				$child = $current->{next};
				if($self->_depth_traverse_in_order($current, $flags, $depth, $funcref, $argref)) {
					return($TRUE);
				}
			}

		} elsif(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($node, $argref)) {
			return($TRUE);
		}

	} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($node, $argref)) {
		return($TRUE);
	}

	return($FALSE);
}

sub _traverse_children() {

	my ($self, $node, $flags, $funcref, $argref) = (shift, shift, shift, shift, shift);
	my $child = $self->new();

	$child = $node->{children};

	while(defined($child)) {

		my $current = $self->new();

		$current = $child;
		$child = $current->{next};

		if(defined($current->{children})) {
			if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($current, $argref)) {
				return($TRUE);
			}
		} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($current, $argref)) {
			return($TRUE);
		}
	}

	$child = $node->{children};

	while(defined($child)) {

		my $current = $self->new();

		$current = $child;
		$child = $current->{next};

		if(defined($current->{children}) && $self->_traverse_children($current, $flags, $funcref, $argref)) {
			return($TRUE);
		}
	}

	return($FALSE);
}

sub _depth_traverse_children() {

	my ($self, $node, $flags, $depth, $funcref, $argref) = (shift, shift, shift, shift, shift, shift);
	my $child = $self->new();

	$child = $node->{children};

	while(defined($child)) {

		my $current = $self->new();

		$current = $child;
		$child = $current->{next};

		if(defined($current->{children})) {

			if(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($current, $argref)) {
				return($TRUE);
			}

		} elsif(($flags & $TRAVERSE_LEAFS) && &$funcref($current, $argref)) {
			return($TRUE);
		}
	}

	$depth--;
	if(!$depth) {
		return($FALSE);
	}

	$child = $node->{children};

	while(defined($child)) {

		my $current = $self->new();

		$current = $child;
		$child = $current->{next};

		if(defined($current->{children}) && $self->_depth_traverse_children($current, $flags, $depth, $funcref, $argref)) {
			return($TRUE);
		}
	}

	return($FALSE);
}

# Traverses a tree starting at the given root node. It calls the given function for each node visited.
# The traversal can be halted at any point by returning TRUE from given function.
sub traverse() {

	my ($self, $root, $order, $flags, $depth, $funcref, $argref) = (shift, shift, shift, shift, shift, shift, shift);

	if(!defined($root)) {
		return;
	}
	if(!defined($funcref)) {
		return;
	}
	if(!($order <= $LEVEL_ORDER)) {
		return;
	}
	if(!($flags <= $TRAVERSE_MASK)) {
		return;
	}
	if(!($depth == -1 || $depth > 0)) {
		return;
	}

	SWITCH:	{

		$order == $PRE_ORDER && do {

			if($depth < 0) {
				$self->_traverse_pre_order($root, $flags, $funcref, $argref);
			} else {
				$self->_depth_traverse_pre_order($root, $flags, $depth, $funcref, $argref);
			}
			last SWITCH;
		};
		$order == $POST_ORDER && do {

			if($depth < 0) {
				$self->_traverse_post_order($root, $flags, $funcref, $argref);
			} else {
				$self->_depth_traverse_post_order($root, $flags, $depth, $funcref, $argref);
			}
			last SWITCH;
		};
		$order == $IN_ORDER && do {

			if($depth < 0) {
				$self->_traverse_in_order($root, $flags, $funcref, $argref);
			} else {
				$self->_depth_traverse_in_order($root, $flags, $depth, $funcref, $argref);
			}
			last SWITCH;
		};
		$order == $LEVEL_ORDER && do {

			if(defined($root->{children})) {
				if(!(($flags & $TRAVERSE_NON_LEAFS) && &$funcref($root, $argref))) {
					if($depth < 0) {
						$self->_traverse_children($root, $flags, $funcref, $argref);
					} else {
						$depth--;
						if($depth) {
							$self->_depth_traverse_children($root, $flags, $depth, $funcref, $argref);
						}
					}
				}
			} elsif($flags & $TRAVERSE_LEAFS) {
				&$funcref($root, $argref);
			}
			last SWITCH;
		};
	} # End SWITCH
}

# Finds a node in a tree.
sub find() {

	my ($self, $root, $order, $flags, $data) = (shift, shift, shift, shift, shift);
	my @d;

	if(!defined($root)) {
		return(undef);
	}
	if(!($order <= $LEVEL_ORDER)) {
		return(undef);
	}
	if(!($flags <= $TRAVERSE_MASK)) {
		return(undef);
	}

	$d[0] = $data;
	$d[1] = undef;

	$self->traverse(
		$root, 
		$order, 
		$flags, 
		-1, 
		sub { 
			my ($node, $ref_of_array) = (shift, shift);

			if($$ref_of_array[0] ne $node->{data}) {
				return($FALSE);
			}

			$$ref_of_array[1] = $node;

			return($TRUE);
		}, 
		\@d
	);

	return($d[1]);
}

# Finds the first child of a node with the given data.
sub find_child() {

	my ($self, $node, $flags, $data) = (shift, shift, shift, shift);

	if(!defined($node)) {
		return(undef);
	}
	if(!($flags <= $TRAVERSE_MASK)) {
		return(undef);
	}

	$node = $node->{children};

	while(defined($node)) {

		if($node->{data} eq $data) {
			if($self->is_leaf($node)) {
				if($flags & $TRAVERSE_LEAFS) {
					return($node);
				}
			} else {
				if($flags & $TRAVERSE_NON_LEAFS) {
					return($node);
				}
			}
		}

		$node = $node->{next};
	}

	return(undef);
}

# Calls a function for each of the children of a node.
# Note that it doesn't descend beneath the child nodes.
sub children_foreach() {

	my ($self, $node, $flags, $funcref, $argref) = (shift, shift, shift, shift, shift);

	if(!defined($node)) {
		return;
	}
	if(!($flags <= $TRAVERSE_MASK)) {
		return;
	}
	if(!defined($funcref)) {
		return;
	}

	$node = $node->{children};

	while(defined($node)) {

		my $current = $self->new();

		$current = $node;
		$node = $current->{next};

		if($self->is_leaf($current)) {
			if($flags & $TRAVERSE_LEAFS) {
				&$funcref($current, $argref);
			}
		} else {
			if($flags & $TRAVERSE_NON_LEAFS) {
				&$funcref($current, $argref);
			}
		}
	}

	return;
}

#
# Sort methods
#

#_pchild_ref is just gathering references
sub _pchild_ref() {

	my ($node, $aref) = (shift, shift);

	push @$aref, $node;
}

# Sort a tree
sub tsort() {

	my ($self, $node) = (shift, shift);
	my @back;

	return if($self->is_leaf($node));

	# gather all the children references and sort them
	# according to the data field backwards (Z Y X W ...)
	$self->children_foreach($node, $Tree::Nary::TRAVERSE_ALL, \&_pchild_ref, \@back);
	@back = sort { $b->{data} cmp $a->{data} } @back;

	for (@back) {                # for every reference found (in backward order)
		$self->unlink($_);         # detach it from parent
		$self->prepend($node, $_); # prepend it 0> first child
		$self->tsort($_);          # call tsort recursively for its children
	}
}

#
# Comparison methods
#

# Generate a normalized tree
sub normalize() {

	my ($self, $node)   = (shift, shift);

	# Initialize result for a leaf
	my $result = '*';

	if(!$self->is_leaf($node)) {

		my @childs;
		my @chldMaps;

		$self->children_foreach($node, $Tree::Nary::TRAVERSE_ALL, \&_pchild_ref, \@childs);

		for(@childs) {
			push @chldMaps, $self->normalize($_);
		}

		$result = '('.join('', sort @chldMaps).')';
	}

	return($result);
}

# Compares two trees and returns TRUE if they are identical
# in their structures and their contents
sub is_identical() {

	my ($self, $t1, $t2) = (shift, shift, shift);
	my $i;
	my @t1childs;
	my @t2childs;

	# Exit if one of them is leaf and the other isn't
	return($FALSE) if(($self->is_leaf($t1) && !$self->is_leaf($t2)) or
		(!$self->is_leaf($t1) && $self->is_leaf($t2)));

	# Exit if they have different amount of children
	return($FALSE) if($self->n_children($t1) != $self->n_children($t2));

	# => HERE BOTH ARE LEAFS OR PARENTS WITH SAME AMOUNT OF CHILDREN

	return($FALSE) if($t1->{data} ne $t2->{data});     # exit if different content
	return($TRUE)  if($self->is_leaf($t1));              # if T1 is leaf, both are: hey, identical!!

	# => HERE BOTH ARE PARENTS WITH SAME AMOUNT OF CHILDREN

	# get the children references for $t1 and $t2
	$self->children_foreach($t1, $Tree::Nary::TRAVERSE_ALL, \&_pchild_ref, \@t1childs);
	$self->children_foreach($t2, $Tree::Nary::TRAVERSE_ALL,\&_pchild_ref, \@t2childs);

	for $i (0 .. scalar(@t1childs)-1) {      # iterate all children by index
		next if($self->is_identical($t1childs[$i], $t2childs[$i]) == $TRUE);
		return($FALSE);
	}

	return($TRUE);
}

# Compare the structure of two trees by comparing their canonical shapes
sub has_same_struct() {

	my ($self, $t1, $t2) = (shift, shift, shift);
	my $t1c = $self->normalize($t1);
	my $t2c = $self->normalize($t2);

	return($TRUE) if($t1c eq $t2c);      # if the two canons are identical, structure is same
	return($FALSE);                      # structure is different
}

1;

__END__

=head1 NAME

Tree::Nary - Perl implementation of N-ary search trees.

=head1 SYNOPSIS

  use Tree::Nary;

  $node = new Tree::Nary;
  $another_node = new Tree::Nary;

  $inserted_node = $node->insert($parent, $position, $node);
  $inserted_node = $node->insert_before($parent, $sibling, $node);
  $inserted_node = $node->append($parent, $node);
  $inserted_node = $node->prepend($parent, $node);
  $inserted_node = $node->insert_data($parent, $position, $data);
  $inserted_node = $node->insert_data_before($parent, $sibling, $data);
  $inserted_node = $node->append_data($parent, $data);
  $inserted_node = $node->prepend_data($parent, $data);

  $node->reverse_children($node);

  $node->traverse($node, $order, $flags, $maxdepth, $funcref, $argref);

  $node->children_foreach($node, $flags, $funcref, $argref);

  $root_node = $obj->get_root($node);

  $found_node = $node->find($node, $order, $flags, $data);
  $found_child_node = $node->find_child($node, $flags, $data);

  $index = $node->child_index($node, $data);
  $position = $node->child_position($node, $child);

  $first_child_node = $node->first_child($node);
  $last_child_node = $node->last_child($node);

  $nth_child_node = $node->nth_child($node, $index);

  $first_sibling = $node->first_sibling($node);
  $next_sibling = $node->next_sibling($node);
  $prev_sibling = $node->prev_sibling($node);
  $last_sibling = $node->last_sibling($node);

  $bool = $node->is_leaf($node);
  $bool = $node->is_root($node);

  $cnt = $node->depth($node);

  $cnt = $node->n_nodes($node);
  $cnt = $node->n_children($node);

  $bool = $node->is_ancestor($node);

  $cnt = $obj->max_height($node);

  $node->tsort($node);

  $normalized_node = $node->normalize($node);

  $bool = $node->is_identical($node, $another_node);
  $bool = $node->has_same_struct($node, $another_node);

  $node->unlink($node);

=head1 DESCRIPTION

The B<Tree::Nary> class implements N-ary trees (trees of data with any 
number of branches), providing the organizational structure for a tree (collection) 
of any number of nodes, but knowing nothing about the specific type of node used. 
It can be used to display hierarchical database entries in an internal application (the
NIS netgroup file is an example of such a database). It offers the capability to select 
nodes on the tree, and attachment points for nodes on the tree. Each attachment point 
can support multiple child nodes.

The data field contains the actual data of the node. The next and previous fields point
to the node's siblings (a sibling is another node with the same parent). The parent
field points to the parent of the node, or is I<undef> if the node is the root of the
tree. The children field points to the first child of the node. The other children are
accessed by using the next pointer of each child.

This module is a translation (albeit not a direct one) from the C implementation of 
N-ary trees, available in the B<GLIB distribution> (see SEE ALSO).

=head1 GLOBAL VARIABLES

=head2 BOOLEANS

=over 4

=item TRUE

=item FALSE

=head2 TRAVERSE FLAGS

Specifies which nodes are visited during several of the tree functions, including
traverse() and find().

=item TRAVERSE_LEAFS 

Specifies that only leaf nodes should be visited.

=item TRAVERSE_NON_LEAFS

Specifies that only non-leaf nodes should be visited.

=item TRAVERSE_ALL 

Specifies that all nodes should be visited.

=item TRAVERSE_MASK

Combination of multiple traverse flags.

=head2 ORDER FLAGS

Specifies the type of traversal performed by traverse() and find(). 

=item PRE_ORDER

Visits a node, then its children.

=item IN_ORDER

Visits a node's left child first, then the node itself, then its right child.
This is the one to use if you want the output sorted according to the compare function.

=item POST_ORDER

Visits the node's children, then the node itself.

=item LEVEL_ORDER

Calls the function for each child of the node, then recursively visits each child.

=head1 METHODS

=head2 new( [DATA] )

Creates a new Tree::Nary object. Used to create the first node in a tree.
Insert optional DATA into new created node.

=head2 insert( PARENT, POSITION, NODE )

Inserts a NODE beneath the PARENT at the given POSITION, returning
inserted NODE. If POSITION is -1, NODE is inserted as the last child
of PARENT.

=head2 insert_before( PARENT, SIBLING, NODE )

Inserts a NODE beneath the PARENT before the given SIBLING, returning 
inserted NODE. If SIBLING is I<undef>, the NODE is inserted as the last child
of PARENT.

=head2 append( PARENT, NODE )

Inserts a NODE as the last child of the given PARENT, returning inserted NODE.

=head2 prepend( PARENT, NODE )

Inserts a NODE as the first child of the given PARENT, returning inserted NODE.

=head2 insert_data( PARENT, POSITION, DATA )

Inserts a B<new> node containing DATA, beneath the PARENT at the given POSITION.
Returns the new inserted node.

=head2 insert_data_before( PARENT, SIBLING, DATA )

Inserts a B<new> node containing DATA, beneath the PARENT, before the given
SIBLING. Returns the new inserted node.

=head2 append_data( PARENT, DATA )

Inserts a B<new> node containing DATA as the last child of the given PARENT.
Returns the new inserted node.

=head2 prepend_data( PARENT, DATA )

Inserts a B<new> node containing DATA as the first child of the given PARENT.
Returns the new inserted node.

=head2 reverse_children( NODE )

Reverses the order of the children of NODE.
It doesn't change the order of the grandchildren.

=head2 traverse( NODE, ORDER, FLAGS, MAXDEPTH, FUNCTION, DATA )

Traverses a tree starting at the given root NODE. It calls the given FUNCTION
(with optional user DATA to pass to the FUNCTION) for each node visited.

The traversal can be halted at any point by returning TRUE from FUNCTION.

The ORDER in which nodes are visited is one of IN_ORDER, PRE_ORDER, POST_ORDER and
LEVEL_ORDER.

FLAGS specifies which types of children are to be visited, one of TRAVERSE_ALL, 
TRAVERSE_LEAFS and TRAVERSE_NON_LEAFS.

MAXDEPTH is the maximum depth of the traversal. Nodes below this depth will not
be visited. If MAXDEPTH is -1, all nodes in the tree are visited. If MAXDEPTH
is 1, only the root is visited. If MAXDEPTH is 2, the root and its children are
visited. And so on.

=head2 children_foreach( NODE, FLAGS, FUNCTION, DATA )

Calls a FUNCTION (with optional user DATA to pass to the FUNCTION) for each
of the children of a NODE. Note that it doesn't descend beneath the child nodes.
FLAGS specifies which types of children are to be visited, one of TRAVERSE_ALL,
TRAVERSE_LEAFS and TRAVERSE_NON_LEAFS.

=head2 get_root( NODE )

Gets the root node of a tree, starting from NODE.

=head2 find( NODE, ORDER, FLAGS, DATA )

Finds a NODE in a tree with the given DATA.

The ORDER in which nodes are visited is one of IN_ORDER, PRE_ORDER, POST_ORDER and
LEVEL_ORDER.

FLAGS specifies which types of children are to be searched, one of TRAVERSE_ALL,
TRAVERSE_LEAFS and TRAVERSE_NON_LEAFS.

Returns the found node, or I<undef> if the DATA is not found.

=head2 find_child( NODE, FLAGS, DATA )

Finds the first child of a NODE with the given DATA.

FLAGS specifies which types of children are to be searched, one of TRAVERSE_ALL,
TRAVERSE_LEAFS and TRAVERSE_NON_LEAFS.

Returns the found child node, or I<undef> if the DATA is not found.

=head2 child_index( NODE, DATA )

Gets the position of the first child of a NODE which contains the given DATA.
Returns the index of the child of node which contains data, or -1 if DATA is
not found. 

=head2 child_position( NODE, CHILD )

Gets the position of a NODE with respect to its siblings. CHILD must be a child
of NODE. The first child is numbered 0, the second 1, and so on. Returns the position
of CHILD with respect to its siblings.

=head2 first_child( NODE )

Returns the first child of a NODE. Returns I<undef> if NODE is I<undef> or has
no children.

=head2 last_child( NODE )

Returns the last child of a NODE. Returns I<undef> if NODE is I<undef> or has
no children.

=head2 nth_child( NODE, INDEX )

Gets a child of a NODE, using the given INDEX. The first child is at INDEX 0.
If the INDEX is too big, I<undef> is returned. Returns the child of NODE at INDEX. 

=head2 first_sibling( NODE )

Returns the first sibling of a NODE. This could possibly be the NODE itself.

=head2 prev_sibling( NODE )

Returns the previous sibling of a NODE.

=head2 next_sibling( NODE )

Returns the next sibling of a NODE.

=head2 last_sibling( NODE )

Returns the last sibling of a NODE. This could possibly be the NODE itself.

=head2 is_leaf( NODE )

Returns TRUE if NODE is a leaf node (no children).

=head2 is_root( NODE )

Returns TRUE if NODE is a root node (no parent nor siblings).

=head2 depth( NODE )

Returns the depth of NODE. If NODE is I<undef>, the depth is 0. The root node has 
a depth of 1. For the children of the root node, the depth is 2. And so on.

=head2 n_nodes( NODE, FLAGS )

Returns the number of nodes in a tree.

FLAGS specifies which types of children are to be counted, one of TRAVERSE_ALL,
TRAVERSE_LEAFS and TRAVERSE_NON_LEAFS.

=head2 n_children( NODE )

Returns the number of children of NODE.

=head2 is_ancestor( NODE, DESCENDANT )

Returns TRUE if NODE is an ancestor of DESCENDANT. This is true if NODE is the
parent of DESCENDANT, or if NODE is the grandparent of DESCENDANT, etc.

=head2 max_height( NODE )

Returns the maximum height of all branches beneath NODE. This is the maximum
distance from NODE to all leaf nodes.

If NODE is I<undef>, 0 is returned. If NODE has no children, 1 is returned.
If NODE has children, 2 is returned. And so on.

=head2 tsort( NODE )

Sorts all the children references of NODE according to the data field.

=head2 normalize( NODE )

Returns the normalized shape of NODE.

=head2 is_identical( NODE, ANOTHER_NODE )

Returns TRUE if NODE and ANOTHER_NODE have same structures and contents.

=head2 has_same_struct( NODE, ANOTHER_NODE )

Returns TRUE if the structure of NODE and ANOTHER_NODE are identical.

=head2 unlink( NODE )

Unlinks NODE from a tree, resulting in two separate trees.
The NODE to unlink becomes the root of a new tree.

=head1 EXAMPLES

An example for each function can be found in the test suite bundled with
B<Tree::Nary>.

=head1 AUTHOR

Frederic Soriano, <fsoriano@cpan.org>

=head1 COPYRIGHT

This package is free software and is provided "as is" without express or
implied warranty.  It may be used, redistributed and/or modified under the
same terms as Perl itself.

=head1 SEE ALSO

API from the GLIB project,
http://developer.gnome.org/doc/API/glib/glib-n-ary-trees.html.

=cut
