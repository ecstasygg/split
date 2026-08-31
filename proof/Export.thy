theory Export
  imports Reuse
begin

definition seed :: memory where
  "seed frame offset = (frame * 17 + offset) mod 256"

definition boot :: pager where "boot = initial 4 seed"

definition read_byte :: "pager \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "read_byte s k offset = view s k offset"

export_code boot initial read_byte checked frontier ptable writable prepare reserve reclaim
  Read Write Suc in OCaml module_name Split file_prefix split

end
