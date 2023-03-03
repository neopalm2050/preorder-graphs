import Lake
open Lake DSL

package preorder {
  -- add package configuration options here
}

lean_lib Preorder {
  -- add library configuration options here
}

lean_lib UniqueList {}

--lean_lib UnionFind {}

@[defaultTarget]
lean_exe preorder {
  root := `Main
}
