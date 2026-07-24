import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_817452_1.RI3_1_817452_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![7855, 1407, 252]

def alpha1 := B.equivFun.symm ![34, 6, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![15661, -2688, -21]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -1313, -612], ![0, -385, 0]], ![![0, 0, 0], ![17425, -100, 0]]], ![![![0, -27, -13], ![0, -4, 0]], ![![0, 0, 0], ![349, -2, 0]]]]
 g := ![![![![0, -1, 0], ![25, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![125, 0, 0], ![26, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![5, 5, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -104, 492], ![-522, -5641, 3]], ![![0, -1335, 0], ![87125, -500, 0]]], ![![![0, -24, 14], ![-522, -722, 3]], ![![0, -269, 0], ![17774, -102, 0]]]]
 g := ![![![![1743, 67, 0], ![-8375, 0, 0]], ![![307, 12, 0], ![-1475, 0, 0]]], ![![![51, 2, 0], ![-245, 0, 0]], ![![-21, -1, 0], ![101, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![26, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![625, 0, 0], ![151, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![125, 125, 0]], ![![130, 5, 0], ![26, 27, 1]]]
 hmul := by decide
 f := ![![![![437077082, 225412810, 8405429], ![-1005277285, -40651765, 0]], ![![-1134367500, -34022500, 0], ![-1742500, -2500, 0]]], ![![![105248662, 54279667, 2024037], ![-242071919, -9788991, 0]], ![![-273156996, -8192680, 0], ![-419596, -602, 0]]]]
 g := ![![![![46811, 310, 0], ![-193750, 0, 0]], ![![9181, 61, 0], ![-38000, 0, 0]]], ![![![9512, 63, 0], ![-39370, 0, 0]], ![![1842, 12, 0], ![-7624, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![151, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![3125, 0, 0], ![1401, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![625, 625, 0]], ![![755, 5, 0], ![151, 152, 1]]]
 hmul := by decide
 f := ![![![![2830755786, -145742891634, 4741317281], ![-6510738305, -28766466025, 0]], ![![-6325275000, 632487075000, 0], ![-8712500, -12500, 0]]], ![![![1268632162, -65316167771, 2124869841], ![-2917853969, -12891986017, 0]], ![![-2834736696, 283455552720, 0], ![-3904596, -5602, 0]]]]
 g := ![![![![1441630, 1029, 0], ![-3215625, 0, 0]], ![![288326, 206, 0], ![-643125, 0, 0]]], ![![![347446, 248, 0], ![-774995, 0, 0]], ![![67808, 48, 0], ![-151249, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![1401, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![7855, 1407, 252]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![3125, 3125, 0]], ![![7005, 5, 0], ![1401, 1402, 1]]]
 hmul := by decide
 f := ![![![![-1034257798058, 254955547813021, -9663690744384], ![2378792935536, 49265222973340, 0]], ![![1245754228019, -591730800135782, 0], ![29833244, 42909, 0]]]]
 g := ![![![![6889, -2289, 189]], ![![7955, 920, -420]]], ![![![3099, -1024, 84]], ![![3543, 415, -188]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![26, 0, 0], ![2, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![34, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![676, 0, 0], ![52, 26, 0]], ![![52, 26, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-38101904, -19080231, 0], ![-3664745, -249825183, 0]], ![![0, 0, 0], ![6496324763, -217501, 0]]]]
 g := ![![![![112, -30, 2]], ![![22, 2, -1]]], ![![![22, 2, -1]], ![![-5, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![235444969, 42173502, 7554225])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![26, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![1, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![130, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![130, 0, 0], ![10, 5, 0]], ![![26, 26, 0], ![2, 3, 1]]]
 hmul := by decide
 f := ![![![![103, 207, 0], ![26, -2704, 0]], ![![-520, 520, 0], ![0, 0, 0]]], ![![![-21, -40, 0], ![21, 520, 0]], ![![96, -100, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![5, 0, 0]]], ![![![5, 0, 0], ![26, 0, 0]], ![![5, 0, 0], ![27, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![130, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![1, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![650, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![650, 0, 0], ![50, 25, 0]], ![![26, 26, 0], ![2, 3, 1]]]
 hmul := by decide
 f := ![![![![-27, 597, 0], ![26, -16224, 0]], ![![650, 15600, 0], ![0, 0, 0]]], ![![![-1, -24, 0], ![25, 624, 0]], ![![-24, -600, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![25, 0, 0]]], ![![![1, 0, 0], ![26, 0, 0]], ![![1, 0, 0], ![27, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![650, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![26, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![125, 0, 0], ![26, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![3250, 0, 0], ![1276, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![3250, 0, 0], ![250, 125, 0]], ![![676, 26, 0], ![52, 28, 1]]]
 hmul := by decide
 f := ![![![![78379, -1172775, 0], ![-39052, -1275274, 0]], ![![-362375, 6131125, 0], ![0, 0, 0]]], ![![![30773, -460440, 0], ![-15335, -500682, 0]], ![![-142274, 2407125, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-49, 0, 0], ![125, 0, 0]]], ![![![-10, 0, 0], ![26, 0, 0]], ![![490, 0, 0], ![-1248, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3250, 0, 0], ![1276, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![151, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![625, 0, 0], ![151, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![16250, 0, 0], ![4526, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![16250, 0, 0], ![1250, 625, 0]], ![![3926, 26, 0], ![302, 153, 1]]]
 hmul := by decide
 f := ![![![![2222418, -110042568, 0], ![-4061434, -19231524, 0]], ![![-7905625, 462296250, 0], ![0, 0, 0]]], ![![![618993, -30649354, 0], ![-1131181, -5356416, 0]], ![![-2201899, 128760000, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-174, 0, 0], ![625, 0, 0]]], ![![![-7, 0, 0], ![26, 0, 0]], ![![1218, 0, 0], ![-4373, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16250, 0, 0], ![4526, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![1401, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![3125, 0, 0], ![1401, 1, 0]] ![![26, 0, 0], ![2, 1, 0]]
  ![![81250, 0, 0], ![4526, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![81250, 0, 0], ![6250, 3125, 0]], ![![36426, 26, 0], ![2802, 1403, 1]]]
 hmul := by decide
 f := ![![![![322066407, -76580322761, 0], ![-2920622666, -1425311524, 0]], ![![-217262500, 171311481250, 0], ![0, 0, 0]]], ![![![17940580, -4265876231, 0], ![-162692093, -79396408, 0]], ![![-12102524, 9542837500, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-174, 0, 0], ![3125, 0, 0]]], ![![![-1, 0, 0], ![26, 0, 0]], ![![174, 0, 0], ![-3123, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81250, 0, 0], ![4526, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
