import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![6, 2, -1]

def alpha1 := B.equivFun.symm ![-101, -4, 5]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![50, 1, -2]

def zeta2 := B.equivFun.symm ![-1, -2, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-16, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![-16, 0, 1]] ![![11, 0, 0], ![-16, 0, 1]]
  ![![121, 0, 0], ![486, -19, -32]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-176, 0, 11]], ![![-176, 0, 11], ![251, 11, -4]]]
 hmul := by decide
 f := ![![![![-16229, -54450, -40776], ![19932, 85668, 0]], ![![0, 0, 0], ![-726, 0, 0]]], ![![![-459940, -1542525, -1155137], ![564015, 2426906, 0]], ![![0, 0, 0], ![-20928, 38, 0]]]]
 g := ![![![![102247, 465710, 1103662], ![45980, 357918, 0]], ![![-148988, -677386, -1605309], ![-66814, -520608, 0]]], ![![![-148988, -677386, -1605309], ![-66814, -520608, 0]], ![![211905, 965230, 2287448], ![95301, 741820, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![486, -19, -32]] ![![11, 0, 0], ![-16, 0, 1]]
  ![![6, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-1936, 0, 121]], ![![5346, -209, -352], ![-7730, -485, 7]]]
 hmul := by decide
 f := ![![![![11136245565224238, 36179259699784760, 27087298857662118], ![-13735693653265947, -56859238912797824, 0]], ![![-25211904817530, 51957571560, 0], ![3552504, -360, 0]]]]
 g := ![![![![271, 11, -7]], ![![-385, 0, 22]]], ![![![1077, -11, -76]], ![![-1538, -83, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![-6, 1, 0]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![289, 0, 0], ![96, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![-102, 17, 0], ![31, -17, 11]]]
 hmul := by decide
 f := ![![![![25467, 60058, -59774], ![-5440, 92480, 0]], ![![0, 0, 0], ![-1734, 0, 0]]], ![![![101507, 239422, -238282], ![-21724, 368656, 0]], ![![0, 0, 0], ![-6918, -7, 0]]]]
 g := ![![![![24963, -494517, -59774], ![6647, 1570426, 0]], ![![-8833, 174637, 21109], ![-2295, -554591, 0]]], ![![![-8833, 174637, 21109], ![-2295, -554591, 0]], ![![2668, -53147, -6424], ![759, 168777, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![289, 0, 0], ![96, 1, 0]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![-101, -4, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-1734, 289, 0]], ![![1632, 17, 0], ![-581, 85, 11]]]
 hmul := by decide
 f := ![![![![-101923667638, -240708436012, 239471530998], ![21813739401, -370083316550, 0]], ![![2323800618, -153832574, 0], ![-159071, -40, 0]]]]
 g := ![![![![-57, -109, -94]], ![![19, -60, -65]]], ![![![-19, -42, -37]], ![![6, -24, -25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, -1, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-51, -1, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![96, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-16, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![11, 0, 0], ![-16, 0, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![187, 0, 0], ![-1413, -112, 80]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![187, 0, 0], ![-66, 11, 0]], ![![-272, 0, 17], ![102, 7, -1]]]
 hmul := by decide
 f := ![![![![142767, 337209, -335480], ![-30549, 518364, 0]], ![![748, 0, 0], ![0, 0, 0]]], ![![![-53404973, -126141453, 125493880], ![11428737, -193906244, 0]], ![![-279828, 672, 0], ![0, 0, 0]]]]
 g := ![![![![-981171, 9298954, -7958592], ![-1556588, -1938442, 0]], ![![348497, -3289365, 2815248], ![550825, 685718, 0]]], ![![![1428057, -13525680, 11576083], ![2264247, 2819552, 0]], ![![-533942, 5067447, -4337011], ![-848152, -1056338, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![187, 0, 0], ![-1413, -112, 80]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![11, 0, 0], ![-16, 0, 1]] ![![289, 0, 0], ![96, 1, 0]]
  ![![3179, 0, 0], ![-25814, 63, 1505]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3179, 0, 0], ![1056, 11, 0]], ![![-4624, 0, 289], ![-1530, 7, 101]]]
 hmul := by decide
 f := ![![![![924185763, -18293659782, -2211221894], ![243696360, 58094769018, 0]], ![![25432, 0, 0], ![0, 0, 0]]], ![![![24253842444, -480089093306, -58030133196], ![6395431778, 1524608269728, 0]], ![![667424, -63, 0], ![0, 0, 0]]]]
 g := ![![![![916385813, 11998304723, 12255800781], ![-1401102923, -4484367338, 0]], ![![304414560, 3985547556, 4071080797], ![-465410979, -1489598726, 0]]], ![![![-1332889618, -17452079683, -17826621370], ![2037972223, 6522716128, 0]], ![![-441031726, -5774616018, -5898545930], ![674332679, 2158263182, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3179, 0, 0], ![-25814, 63, 1505]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![486, -19, -32]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![121, 0, 0], ![486, -19, -32]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![2057, 0, 0], ![-2092, 70, 124]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2057, 0, 0], ![-726, 121, 0]], ![![8262, -323, -544], ![-3013, -41, -177]]]
 hmul := by decide
 f := ![![![![113995910194768, 269227981032929, -267883847418233], ![-24396910596204, 413914089907098, 0]], ![![-215893636288, 4091373, 0], ![0, 0, 0]]], ![![![-116011623264226, -273988558487916, 272620657461830], ![24828304770448, -421233054589568, 0]], ![![219711138368, -4163718, 0], ![0, 0, 0]]]]
 g := ![![![![669367423, 1143792630, 3855180906], ![-409433508, -5668588035, 0]], ![![-236264992, -403724307, -1360762526], ![144519133, 2000840391, 0]]], ![![![2688580896, 4594163711, 15484740430], ![-1644536616, -22768480953, 0]], ![![-980449801, -1675364393, -5646856333], ![599718206, 8303034834, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2057, 0, 0], ![-2092, 70, 124]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![121, 0, 0], ![486, -19, -32]] ![![289, 0, 0], ![96, 1, 0]]
  ![![34969, 0, 0], ![171278, 17456, -9278]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![34969, 0, 0], ![11616, 121, 0]], ![![140454, -5491, -9248], ![46559, -1979, -3441]]]
 hmul := by decide
 f := ![![![![2032021761784487709, -40222557220001016111, -4861848211402179956], ![535818449520103337, 127733871421007120401, 0]], ![![-20247807169656, 80253855, 0], ![0, 0, 0]]], ![![![9932943866662141574, -196616202913603112086, -23765722533246861158], ![2619191724172880610, 624389658889325859438, 0]], ![![-98975481376032, 392297490, 0], ![0, 0, 0]]]]
 g := ![![![![-2178072368777, 19747367371744, -23860862756398], ![5520182665987, 6081378081548, 0]], ![![-723511623410, 6559675383861, -7926095223692], ![1833692874365, 2020110600893, 0]]], ![![![-8748309059196, 79316041653337, -95838050118004], ![22172020638533, 24426083131177, 0]], ![![-2899971513783, 26292425072321, -31769295332233], ![7349789265871, 8096987030349, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![34969, 0, 0], ![171278, 17456, -9278]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
