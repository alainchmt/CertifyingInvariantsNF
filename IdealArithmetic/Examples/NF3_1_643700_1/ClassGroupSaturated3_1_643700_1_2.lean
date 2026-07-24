import IdealArithmetic.Examples.NF3_1_643700_1.ClassGroupData3_1_643700_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq17 : Fact $ Nat.Prime 17 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

def R17 : IsOrderOf (3 : ZMod 17) 16 where
 m := 1
 P := ![2]
 e := ![4]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![11, 0, -1]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-4, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-4, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![11, 0, -1]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![11, 0, -1], ![183, -8, -3], ![143, 21, -10]]]
  hmulB := by decide  
  f := ![![![-10, 0, 1], ![3, 0, 0]], ![![-6, 3, -4], ![-15, 1, 0]], ![![4, 0, 0], ![-1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![4, 0, -1], ![62, -8, -3], ![51, 21, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-4, 1, 0]] 
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-4, 1, 0], ![3, -6, 6], ![-183, 19, -1]]]
  hmulB := by decide  
  f := ![![![51, -107, 108], ![-13, -234, 0]], ![![33, -71, 72], ![-12, -156, 0]], ![![13, -25, 25], ![1, -54, 0]]]
  g := ![![![1, 0, 0], ![-9, 13, 0], ![-3, 0, 13]], ![![-1, 1, 0], ![3, -6, 6], ![-27, 19, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-4, 1, 0]] 
 ![![17, 0, 0], ![13, 1, 0], ![5, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-4, 1, 0], ![3, -6, 6], ![-183, 19, -1]]]
  hmulB := by decide  
  f := ![![![181, -381, 384], ![-51, -1088, 0]], ![![137, -286, 288], ![-33, -816, 0]], ![![53, -112, 113], ![-16, -320, 0]]]
  g := ![![![1, 0, 0], ![-13, 17, 0], ![-5, 0, 17]], ![![-1, 1, 0], ![3, -6, 6], ![-25, 19, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 17 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461501, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1805784794721061118862602664006348302717170811858626199424474932591436169603729653134560899072501072032562467, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461499, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hxeq :=  rfl
 m := 2
 C := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461501, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] ![1314841706305738, -65469205166340, -83594671704068] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![466145459336602, -65469205166340, -83594671704068]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1314841706305739, -65469205166340, -83594671704068]
 hxeq :=  rfl
 m := 1
 C := ![1314841706305738, -65469205166340, -83594671704068]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461504, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1164819088752498635930770932661921333624204755144033926343296990971203941661217580020466002812140208086269010, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461499, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hxeq :=  rfl
 m := 5
 C := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461504, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] ![-13, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] ![1314841706305727, -65469205166340, -83594671704068] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![165757582147307, -65469205166340, -83594671704068]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1314841706305739, -65469205166340, -83594671704068]
 hxeq :=  rfl
 m := 12
 C := ![1314841706305727, -65469205166340, -83594671704068]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![17, 0, 0], ![13, 1, 0], ![5, 0, 1]] ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461506, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1117549006799038419542873646395687599885737663130040332823889109277159536422870821693563565960591001238699164, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461499, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hxeq :=  rfl
 m := 7
 C := ![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461506, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![17, 0, 0], ![13, 1, 0], ![5, 0, 1]] ![-17, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 16
 C := ![-17, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![17, 0, 0], ![13, 1, 0], ![5, 0, 1]] ![1314841706305729, -65469205166340, -83594671704068] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![151994984234617, -65469205166340, -83594671704068]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1314841706305739, -65469205166340, -83594671704068]
 hxeq :=  rfl
 m := 10
 C := ![1314841706305729, -65469205166340, -83594671704068]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

end Sat2
