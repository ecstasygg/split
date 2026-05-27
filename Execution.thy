theory Execution
  imports Isolation
begin

datatype action = Read nat nat | Write nat nat nat

fun valid :: "nat \<Rightarrow> nat \<Rightarrow> action \<Rightarrow> bool" where
  "valid slots bytes (Read k offset) = (k < slots \<and> offset < bytes)"
| "valid slots bytes (Write k offset byte) = (k < slots \<and> offset < bytes \<and> byte < 256)"

fun advance :: "pager \<Rightarrow> action \<Rightarrow> pager" where
  "advance s (Read k offset) = s"
| "advance s (Write k offset byte) = store s k offset byte"

fun reference :: "memory \<Rightarrow> action \<Rightarrow> memory" where
  "reference m (Read k offset) = m"
| "reference m (Write k offset byte) = reference_write m k offset byte"

fun observe :: "pager \<Rightarrow> action \<Rightarrow> nat" where
  "observe s (Read k offset) = view s k offset"
| "observe s (Write k offset byte) = byte"

fun reference_observe :: "memory \<Rightarrow> action \<Rightarrow> nat" where
  "reference_observe m (Read k offset) = m k offset"
| "reference_observe m (Write k offset byte) = byte"

fun execute :: "pager \<Rightarrow> action list \<Rightarrow> pager" where
  "execute s [] = s"
| "execute s (a # actions) = execute (advance s a) actions"

fun reference_execute :: "memory \<Rightarrow> action list \<Rightarrow> memory" where
  "reference_execute m [] = m"
| "reference_execute m (a # actions) = reference_execute (reference m a) actions"

fun observations :: "pager \<Rightarrow> action list \<Rightarrow> nat list" where
  "observations s [] = []"
| "observations s (a # actions) = observe s a # observations (advance s a) actions"

fun reference_observations :: "memory \<Rightarrow> action list \<Rightarrow> nat list" where
  "reference_observations m [] = []"
| "reference_observations m (a # actions) =
    reference_observe m a # reference_observations (reference m a) actions"

lemma advance_invariant:
  "invariant n s \<Longrightarrow> invariant n (advance s a)"
  by (cases a; simp add: write_invariant)

lemma advance_simulation:
  "invariant n s \<Longrightarrow> represents n s m \<Longrightarrow> valid n bytes a \<Longrightarrow>
   represents n (advance s a) (reference m a)"
  by (cases a; auto intro: simulation)

lemma observe_simulation:
  "represents n s m \<Longrightarrow> valid n bytes a \<Longrightarrow>
   observe s a = reference_observe m a"
  by (cases a; auto simp: represents_def)

theorem execute_invariant:
  "invariant n s \<Longrightarrow> invariant n (execute s actions)"
  by (induction actions arbitrary: s) (auto intro: advance_invariant)

theorem execute_refinement:
  assumes "invariant n s" "represents n s m" "list_all (valid n bytes) actions"
  shows "represents n (execute s actions) (reference_execute m actions)"
  using assms
  by (induction actions arbitrary: s m)
     (auto intro: advance_invariant advance_simulation)

theorem observable_equivalence:
  assumes "invariant n s" "represents n s m" "list_all (valid n bytes) actions"
  shows "observations s actions = reference_observations m actions"
  using assms
  by (induction actions arbitrary: s m)
     (auto intro: advance_invariant advance_simulation observe_simulation)

definition admitted :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> action \<Rightarrow> bool" where
  "admitted slots bytes capacity s a \<longleftrightarrow> valid slots bytes a \<and>
    (case a of Read k offset \<Rightarrow> True
     | Write k offset byte \<Rightarrow> writable s k \<or> frontier s < capacity)"

definition checked :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pager \<Rightarrow> action \<Rightarrow> pager option" where
  "checked slots bytes capacity s a =
    (if admitted slots bytes capacity s a then Some (advance s a) else None)"

lemma checked_failure:
  "\<not> admitted slots bytes capacity s a \<Longrightarrow> checked slots bytes capacity s a = None"
  by (simp add: checked_def)

lemma checked_success:
  "checked slots bytes capacity s a = Some t \<Longrightarrow> t = advance s a"
  by (auto simp: checked_def split: if_splits)

theorem checked_invariant:
  "invariant slots s \<Longrightarrow> checked slots bytes capacity s a = Some t \<Longrightarrow>
   invariant slots t"
  using checked_success advance_invariant by blast

theorem checked_capacity:
  "frontier s \<le> capacity \<Longrightarrow> checked slots bytes capacity s a = Some t \<Longrightarrow>
   frontier t \<le> capacity"
  by (cases a; auto simp: checked_def admitted_def prepare_frontier split: if_splits)

theorem checked_simulation:
  "invariant slots s \<Longrightarrow> represents slots s m \<Longrightarrow>
   checked slots bytes capacity s a = Some t \<Longrightarrow>
   represents slots t (reference m a)"
  by (auto simp: checked_def admitted_def split: if_splits intro: advance_simulation)

lemma invalid_slot_rejected:
  "slots \<le> k \<Longrightarrow> checked slots bytes capacity s (Write k offset byte) = None"
  by (simp add: checked_def admitted_def)

lemma invalid_offset_rejected:
  "bytes \<le> offset \<Longrightarrow> checked slots bytes capacity s (Write k offset byte) = None"
  by (simp add: checked_def admitted_def)

lemma invalid_byte_rejected:
  "256 \<le> byte \<Longrightarrow> checked slots bytes capacity s (Write k offset byte) = None"
  by (simp add: checked_def admitted_def)

lemma exhausted_readonly_rejected:
  "\<not> writable s k \<Longrightarrow> capacity \<le> frontier s \<Longrightarrow>
   checked slots bytes capacity s (Write k offset byte) = None"
  by (simp add: checked_def admitted_def)

lemma exhausted_writable_allowed:
  "writable s k \<Longrightarrow> valid slots bytes (Write k offset byte) \<Longrightarrow>
   checked slots bytes capacity s (Write k offset byte) = Some (store s k offset byte)"
  by (simp add: checked_def admitted_def)

end
