import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF7_1_57627615_1.RI7_1_57627615_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1, 1, -1, 3, 0, 1, -2]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-1, 4, 1, 6, 0, 1, -3]

def zeta2 := B.equivFun.symm ![2, 1, 3, 4, 1, 0, -2]

def zeta3 := B.equivFun.symm ![-1, 3, 1, 6, 0, 1, -3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0, 0], ![-1, -4, -2, -4, -1, 0, 2]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0, 0, 0, 0, 0], ![-1, -4, -2, -4, -1, 0, 2]] ![![3, 0, 0, 0, 0, 0, 0], ![-1, -4, -2, -4, -1, 0, 2]]
  ![![9, 0, 0, 0, 0, 0, 0], ![1, 31, 19, 43, 3, 5, -22]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0, 0, 0, 0, 0], ![-3, -12, -6, -12, -3, 0, 6]], ![![-3, -12, -6, -12, -3, 0, 6], ![1, 4, 10, 16, 3, 5, -13]]]
 hmul := by decide
 f := ![![![![126039926, -932469817, 750981643, -672425629, 466095962, 245046100, -414175894], ![-628654170, 740919474, -988082136, 17111772, 9487008, 94068, 0]], ![![0, 0, 0, 0, 0, 0, 0], ![6309, 2088, -1944, -153, 18, 0, 0]]], ![![![-127431029232, 942761827985, -759266318189, 679844085982, -471235871485, -247753421501, 418748593279], ![635592998553, -749095780045, 998984710584, -17298874366, -9594020016, -95554789, 0]], ![![0, 0, 0, 0, 0, 0, 0], ![-6492383, -2231592, 2170638, 165792, -21042, 192, 0]]]]
 g := ![![![![131308415, 51811151, 34313417, -58539202, 59504757, -39021460, 18315616], ![-60812505, 218620008, 301509, -26957304, -60300, 270, 0]], ![![-467476013, -184454783, -122160527, 208407526, -211845336, 138921802, -65206048], ![216500937, -778317360, -1073187, 95972016, 214638, -960, 0]]], ![![![-467476013, -184454783, -122160527, 208407526, -211845336, 138921802, -65206048], ![216500937, -778317360, -1073187, 95972016, 214638, -960, 0]], ![![417129391, 164589130, 109003958, -185962340, 189029934, -123960117, 58183456], ![-193184045, 694493523, 957501, -85636080, -191502, 855, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0, 0, 0, 0, 0], ![1, 31, 19, 43, 3, 5, -22]] ![![3, 0, 0, 0, 0, 0, 0], ![-1, -4, -2, -4, -1, 0, 2]]
  ![![-1, 1, -1, 3, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0, 0, 0, 0, 0], ![-9, -36, -18, -36, -9, 0, 18]], ![![3, 93, 57, 129, 9, 15, -66], ![27, -30, -2, -72, 4, -20, 41]]]
 hmul := by decide
 f := ![![![![-1212064267016854914410, 8516032876866051209012, -7064714390167575598959, 6168568706442514776308, -4359877438709962203510, -2304432637039039248140, 3925720601719458748308], ![5759509105434562783574, -6936384336425023702382, 9343480293108410391306, -50883216086302838094, -26227673435898358060, -77911165026526874, 0]], ![![-1592462339144040, -330105039360893, 43577285466034, 73209355648344, -8716005633824, 108591356248, 0], ![285665026, 4126477, -942951, -33117, 1192, 26, 0]]]]
 g := ![![![![-17, -6, -16, 9, 5, 2, -5]], ![![-1, 33, 7, 27, -5, -2, -4]]], ![![![5, -63, -41, -102, -8, -8, 47]], ![![-18, 2, 11, 36, 10, 8, -25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, -1, 0, 0, 0, 0, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, 0, -2, -1, -1, 0, 1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1, 1, -4, -1, -1, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0, 0], ![-1, -4, -2, -4, -1, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0, 0, 0, 0, 0], ![1, 31, 19, 43, 3, 5, -22]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
