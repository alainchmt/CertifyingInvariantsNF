import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_374220_1.RI3_1_374220_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![274679, 32001, 8781]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2699, 675, 18]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![14, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-429313, 237427, -11318], ![-1056859, 47754, 0]], ![![0, 0, 0], ![43796, -96, 0]]], ![![![-1180626, 652933, -31125], ![-2906400, 131326, 0]], ![![0, 0, 0], ![120440, -264, 0]]]]
 g := ![![![![-9, -1, -1], ![5, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-2, 1, 0], ![0, 0, 0]], ![![-2, -1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![5, 0, 0], ![14, 1, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![24, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![70, 5, 5], ![86, -6, -1]]]
 hmul := by decide
 f := ![![![![20499, -11155, 523], ![50385, -2635, 0]], ![![0, 0, 0], ![-100, 0, 0]]], ![![![19680, -10709, 502], ![48372, -2529, 0]], ![![0, 0, 0], ![-96, 0, 0]]]]
 g := ![![![![6817, 428, -148], ![6580, -2880, 0]], ![![-2794, -175, 60], ![-2676, 1176, 0]]], ![![![19054, 1196, -412], ![18345, -8040, 0]], ![![23558, 1478, -509], ![22660, -9936, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![25, 0, 0], ![24, 1, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![9, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![120, 5, 5], ![66, 4, -1]]]
 hmul := by decide
 f := ![![![![11881743371, -6546924234, 314892407], ![29608831095, -1566936214, 0]], ![![-38210933, 0, 0], ![-2883844, 6324, 0]]], ![![![4193559395, -2310680744, 111138573], ![10450182935, -553036691, 0]], ![![-13486221, 0, 0], ![-1017828, 2232, 0]]]]
 g := ![![![![-4, 4, -1], ![25, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![5, 0, 0]], ![![-6, 4, -1], ![24, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![25, 0, 0], ![9, -4, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![125, 0, 0], ![-16, 21, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![45, -20, 5], ![96, -1, -6]]]
 hmul := by decide
 f := ![![![![1252922, -688990, 31816], ![3122680, -157275, 0]], ![![-9625, 0, 0], ![-500, 0, 0]]], ![![![-160376, 88193, -4073], ![-399708, 20134, 0]], ![![1232, 0, 0], ![64, 0, 0]]]]
 g := ![![![![38185, -10545, 7239], ![-6495, -42780, 0]], ![![-15378, 4240, -2917], ![2669, 17236, 0]]], ![![![13833, -3818, 2623], ![-2370, -15500, 0]], ![![29336, -8107, 5560], ![-4946, -32860, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![125, 0, 0], ![-16, 21, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![125, 0, 0], ![34, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![625, 0, 0], ![-250, 125, 0]], ![![-80, 105, 5], ![146, -76, 19]]]
 hmul := by decide
 f := ![![![![-96341811887, 52657375122, -2217932166], ![-240720545003, 11106703463, 0]], ![![-421094817, 0, 0], ![-1308764, -151, 0]]], ![![![-26159052564, 14297707472, -602220396], ![-65361251430, 3015729453, 0]], ![![-114337080, 0, 0], ![-355360, -41, 0]]]]
 g := ![![![![-29, 4, -1], ![125, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-2, 1, 0], ![5, 0, 0]], ![![-4, 0, 0], ![19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![125, 0, 0], ![34, -4, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![625, 0, 0], ![159, 121, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![625, 0, 0], ![-250, 125, 0]], ![![170, -20, 5], ![46, 24, -6]]]
 hmul := by decide
 f := ![![![![110878429, -61174113, 2882782], ![277022635, -14403855, 0]], ![![-254375, 0, 0], ![-2500, 0, 0]]], ![![![28207443, -15562678, 733379], ![70474485, -3664337, 0]], ![![-64713, 0, 0], ![-636, 0, 0]]]]
 g := ![![![![-53, -22, 42], ![370, -220, 0]], ![![-139, -113, -18], ![481, 89, 0]]], ![![![-88, -62, 11], ![390, -60, 0]], ![![-11, -7, 3], ![55, -16, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![625, 0, 0], ![159, 121, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![625, 0, 0], ![-91, 246, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![3125, 0, 0], ![-1250, 625, 0]], ![![795, 605, 5], ![-204, -101, 119]]]
 hmul := by decide
 f := ![![![![89453568937393242, -49829924243138284, 2559390751535063], ![223603198320350722, -12796587896854867, 0]], ![![-48280607779459, 0, 0], ![107052345409, -7891224, 0]]], ![![![-12996619081723578, 7239739587276476, -371851308719362], ![-32487083841882292, 1859203388046095, 0]], ![![7014640956169, 0, 0], ![-15553527619, 1146508, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![89, -245, -1], ![625, 0, 0]]], ![![![2, -1, 0], ![5, 0, 0]], ![![17, -47, 0], ![119, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![625, 0, 0], ![-91, 246, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![274679, 32001, 8781]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![3125, 0, 0], ![-1250, 625, 0]], ![![-455, 1230, 5], ![296, -601, 244]]]
 hmul := by decide
 f := ![![![![-1058648079964, 572887638275, -21665786683], ![-2646359804218, 108335091073, 0]], ![![-716088153, 0, 0], ![-1098716, 0, 0]]]]
 g := ![![![![-767, 123, 24]], ![![854, -289, 15]]], ![![![1211, -489, 43]], ![![496, 283, -115]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![15954679, 1858761, 510039])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![14, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![24, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![9, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![-16, 21, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![34, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![159, 121, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![-91, 246, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
