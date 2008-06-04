#open "binarytrees.def".

#theorem bt_equal_sym "pi x\ y\ bt_equal x y => bt_equal y x".
prove.

#theorem bt_equal_sym "pi x\ bt x => bt_equal x x".
prove.

#theorem bt_subtree_ref "pi x\ bt x => bt_subtree x x".
prove.

#theorem bt_subtree_trans
  "pi x\ y\ z\ bt x => bt y => bt z => bt_subtree x y => bt_subtree y z =>
  bt_subtree x z".
prove.
