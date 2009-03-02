#open "binarytrees.def".

#theorem bt_equal_sym "pi x\ y\ bt_equal x y => bt_equal y x".
prove.

#theorem bt_equal_refl "pi x\ bt x => bt_equal x x".
prove.

#theorem bt_subtree_refl "pi x\ bt x => bt_subtree x x".
prove.

#theorem bt_subtree_eq "pi x\ bt_equal x y => bt_subtree x y, bt_subtree y x".
prove.

#theorem bt_subtree_eq "pi x\ bt_subtree x y, bt_subtree y x => bt_equal x y".
prove.

#theorem bt_subtree_trans
  "pi x\ y\ z\ bt x => bt y => bt z => bt_subtree x y => bt_subtree y z =>
  bt_subtree x z".
prove.

#theorem bt_size "pi x\n\ bt x => bt_size x n => nat n".
prove.

%#theorem bt_subtree_size
%  "pi x\y\m\n\ bt_subtree x y => bt_size x m => bt_size y n => leq m n".
%prove.

