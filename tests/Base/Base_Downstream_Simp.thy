(* Plan section 7 test 7: the fixture of the downstream row -- a light lemma foo [simp] in a base
   session is a global simp rule downstream; the standard locale's twin is not. *)
theory Base_Downstream_Simp
  imports "Light_Locale.Light_Locale"
begin

consts kd :: "nat set \<Rightarrow> nat"  kd0 :: "nat set \<Rightarrow> nat"
axiomatization where kd_ax: "kd S = 0" and kd0_ax: "kd0 S = 0"

light_locale LFds = fixes S :: "nat set" assumes "finite S"
locale Dds = fixes S :: "nat set" assumes "finite S"

lemma (in LFds) foo [simp]: "kd S = 0" by (rule kd_ax)
lemma (in Dds) foo0 [simp]: "kd0 S = 0" by (rule kd0_ax)

light_locale Setting_ds = fixes n :: nat
lemma (in Setting_ds) bar [simp]: "kd {n} = 0" by (rule kd_ax)

end
