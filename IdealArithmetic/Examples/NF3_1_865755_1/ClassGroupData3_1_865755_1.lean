import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![18, 2, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-4036545, -516692, 241930]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![3, 3, 5]]]
 hmul := by decide
 f := ![![![![32018, 30817, 112320], ![31420, -42120, 0]], ![![0, 0, 0], ![-5608, -4, 0]]], ![![![8004, 7704, 28080], ![7856, -10530, 0]], ![![0, 0, 0], ![-1402, -1, 0]]]]
 g := ![![![![0, -1, 0], ![4, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![7, 7, 20], ![5, -15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![3, 3, 5]]]
 hmul := by decide
 f := ![![![![1048520, 1047319, 4043520], ![1047920, -1572480, 0]], ![![190912, -84240, 0], ![-11216, -8, 0]]], ![![![131065, 130915, 505440], ![130990, -196560, 0]], ![![23864, -10530, 0], ![-1402, -1, 0]]]]
 g := ![![![![0, -1, 0], ![8, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-6, -6, -15], ![1, 25, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![2, 2, 0], ![3, 3, 5]]]
 hmul := by decide
 f := ![![![![5054600, 5053399, 19206720], ![5054000, -7581600, 0]], ![![831104, -393120, 0], ![-22432, -16, 0]]], ![![![315912, 315837, 1200420], ![315876, -473850, 0]], ![![51944, -24570, 0], ![-1402, -1, 0]]]]
 g := ![![![![0, -1, 0], ![16, 0, 0]], ![![0, 0, 0], ![8, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-8, -8, -20], ![1, 65, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![-15, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![2, 2, 0], ![3, 3, 5]]]
 hmul := by decide
 f := ![![![![-35967053, -35969379, -135748080], ![-35968214, 53951160, 0]], ![![-5482382, 2828085, 0], ![-86894, -62, 0]]], ![![![17983112, 17984275, 67872480], ![17983696, -26974960, 0]], ![![2741128, -1414010, 0], ![43446, 31, 0]]]]
 g := ![![![![-6980, 66235, -23715], ![5344, 151776, 0]], ![![-3271, 31169, -11160], ![2544, 71424, 0]]], ![![![-407, 3896, -1395], ![322, 8928, 0]], ![![-613, 5907, -2115], ![497, 13537, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-15, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![64, 0, 0], ![17, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![-30, 2, 0], ![-13, -13, 5]]]
 hmul := by decide
 f := ![![![![244185117154, -85623899329, -279496918095], ![-83437643708, 111122885976, 0]], ![![670432042728, 10814014414, 0], ![169820, -124, 0]]], ![![![61047711598, -21406477075, -69875868965], ![-20859900346, 27781373306, 0]], ![![167611943218, 2703567035, 0], ![42456, -31, 0]]]]
 g := ![![![![-105490, -1055059, -293265], ![-44480, 3753792, 0]], ![![-51667, -516763, -143640], ![-21792, 1838592, 0]]], ![![![49502, 495231, 137655], ![20930, -1761984, 0]], ![![20977, 209849, 58330], ![8865, -746623, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![17, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![128, 0, 0], ![17, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![34, 2, 0], ![19, 19, 5]]]
 hmul := by decide
 f := ![![![![13567525414984, 18720158838095, 12339813702900], ![-29805334901498, -4948806173162, 57242385208]], ![![-6453628874040, 412182324052, 0], ![-355512, -248, 0]]], ![![![1695978806888, 2340072465879, 1542511392525], ![-3725750627725, -618614679710, 7155459026]], ![![-806721746454, 51523948899, 0], ![-44440, -31, 0]]]]
 g := ![![![![-25744, -237937, -66105], ![-5248, 1692288, 0]], ![![-12772, -117916, -32760], ![-2496, 838656, 0]]], ![![![-6850, -63170, -17550], ![-1278, 449280, 0]], ![![-3798, -35094, -9750], ![-767, 249601, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![17, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![256, 0, 0], ![-111, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![128, 128, 0]], ![![34, 2, 0], ![19, 19, 5]]]
 hmul := by decide
 f := ![![![![4278093266976, 6347346081783, 1834832728620], ![-11949230583772, -735392967138, 18288754742]], ![![-909749611120, 93432404136, 0], ![-711024, -496, 0]]], ![![![-1871659789920, -2776954987048, -802736739270], ![5227771580851, 321733389270, -8001304486]], ![![398014175938, -40876545457, 0], ![311072, 217, 0]]]]
 g := ![![![![-40796, 2945795, -133905], ![29440, 6855936, 0]], ![![-20161, 1459863, -66360], ![14720, 3397632, 0]]], ![![![-5333, 391034, -17775], ![4098, 910080, 0]], ![![-3006, 217242, -9875], ![2177, 505601, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![-111, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![18, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![256, 256, 0]], ![![-222, 2, 0], ![-109, -109, 5]]]
 hmul := by decide
 f := ![![![![-269164704240, -945059609314, -616056233263], ![1431402846853, 246006293592, 0]], ![![1598176183335, 53273543332, 0], ![36505, -31, 0]]]]
 g := ![![![![-107, -16, -3]], ![![-488, -128, -40]]], ![![![43, 6, 1]], ![![167, 47, 15]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-4755097947041, -990766108924, -278746166190])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-15, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![17, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![17, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![-111, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
