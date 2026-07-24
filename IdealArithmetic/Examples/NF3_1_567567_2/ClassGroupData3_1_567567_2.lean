import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_567567_2.RI3_1_567567_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-506, -19, -17]

def alpha1 := B.equivFun.symm ![-391, 90, 48]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![2340353776825, -634049478990, -85780584906]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![18, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![4, 0, 0], ![20, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![36, 2, 2]], ![![36, 2, 2], ![464, 15, 11]]]
 hmul := by decide
 f := ![![![![552168, -3494622, -671013], ![2886748, -513540, 0]], ![![0, 0, 0], ![-728, -4, 0]]], ![![![2761610, -17477845, -3355973], ![14437650, -2568396, 0]], ![![0, 0, 0], ![-3641, -20, 0]]]]
 g := ![![![![4, -11, -2], ![20, -4, 0]], ![![26, -99, -18], ![182, -36, 0]]], ![![![26, -99, -18], ![182, -36, 0]], ![![529, -1269, -226], ![2307, -464, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![-506, -19, -17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![72, 4, 4]], ![![40, 2, 2], ![500, 17, 13]]]
 hmul := by decide
 f := ![![![![-53694100436, 340275167398, 65127770427], ![-280545434956, 50000612480, 0]], ![![383450157, 64034382, 0], ![84015, 506, 0]]]]
 g := ![![![![-19, 5, 1]], ![![105, -27, -7]]], ![![![43, -11, -3]], ![![-235, 58, 20]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![25, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-5, 5, 0], ![3, -1, 4]]]
 hmul := by decide
 f := ![![![![-2334803, -85772, -4844752], ![449810, 6031750, 0]], ![![0, 0, 0], ![120650, -150, 0]]], ![![![124509, 4573, 258356], ![-23982, -321655, 0]], ![![0, 0, 0], ![-6434, 8, 0]]]]
 g := ![![![![625, 0, 1248], ![0, -7800, 0]], ![![-129, -1, -260], ![30, 1625, 0]]], ![![![-129, -1, -260], ![30, 1625, 0]], ![![76, 0, 152], ![-1, -949, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![-391, 90, 48]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![-25, 25, 0]], ![![-5, 5, 0], ![3, -1, 4]]]
 hmul := by decide
 f := ![![![![-1930868545, -66425502, -3994575964], ![372888613, 5013615669, 0]], ![![-204158283, -101571220, 0], ![-2031686, 2526, 0]]]]
 g := ![![![![3116797, 117018, 104736]], ![![1539115, 57785, 51720]]], ![![![307823, 11557, 10344]], ![![152007, 5707, 5108]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![56503491636128342327196121, 2121384714553755638749602, 1898727948922780802812542])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![18, 1, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![10, 0, 0], ![22, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-2, 2, 0]], ![![90, 5, 5], ![85, -9, 2]]]
 hmul := by decide
 f := ![![![![-189346, -7514, -387257], ![36370, 483840, 0]], ![![400, -10, 0], ![0, 0, 0]]], ![![![-416008, -16508, -850832], ![79903, 1063032, 0]], ![![879, -22, 0], ![0, 0, 0]]]]
 g := ![![![![8056, -3532, -389], ![17360, -4490, 0]], ![![-1644, 719, 79], ![-3532, 914, 0]]], ![![![72521, -31752, -3493], ![156045, -40370, 0]], ![![68683, -30076, -3309], ![147803, -38237, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![22, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![18, 1, 1]] ![![25, 0, 0], ![-1, 1, 0]]
  ![![50, 0, 0], ![12, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![-2, 2, 0]], ![![450, 25, 25], ![85, -9, 2]]]
 hmul := by decide
 f := ![![![![-158899774, -259026, -318137277], ![6345650, 1988327200, 0]], ![![10000, -50, 0], ![0, 0, 0]]], ![![![-38119586, -62140, -76320193], ![1522313, 476993822, 0]], ![![2399, -12, 0], ![0, 0, 0]]]]
 g := ![![![![3017752, -447904, 78569], ![716900, -1548450, 0]], ![![-120824, 17932, -3146], ![-28682, 61994, 0]]], ![![![27158452, -4030929, 707090], ![6451575, -13935350, 0]], ![![5130668, -761510, 133580], ![1218853, -2632617, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![12, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![20, 1, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![20, 0, 0], ![12, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![-4, 4, 0]], ![![100, 5, 5], ![83, -7, 2]]]
 hmul := by decide
 f := ![![![![-1167995, -45385, -2409267], ![224525, 3011040, 0]], ![![1800, -20, 0], ![0, 0, 0]]], ![![![-698730, -27151, -1441297], ![134319, 1801296, 0]], ![![1077, -12, 0], ![0, 0, 0]]]]
 g := ![![![![40244, -8593, 400], ![23740, -10580, 0]], ![![-8180, 1744, -82], ![-4804, 2148, 0]]], ![![![201071, -42932, 1999], ![118605, -52860, 0]], ![![167223, -35707, 1662], ![98651, -43963, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![12, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![20, 1, 1]] ![![25, 0, 0], ![-1, 1, 0]]
  ![![100, 0, 0], ![12, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![-4, 4, 0]], ![![500, 25, 25], ![83, -7, 2]]]
 hmul := by decide
 f := ![![![![-936239428, -1506972, -1875036327], ![37389300, 11718907200, 0]], ![![45000, -100, 0], ![0, 0, 0]]], ![![![-112285590, -180736, -224877906], ![4484219, 1405478536, 0]], ![![5397, -12, 0], ![0, 0, 0]]]]
 g := ![![![![1296704, -180308, 36765], ![154200, -1276900, 0]], ![![-51984, 7228, -1474], ![-6164, 51188, 0]]], ![![![6482820, -901440, 183806], ![770825, -6383800, 0]], ![![1076456, -149684, 30520], ![128071, -1060023, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![12, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
