import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_607500000_4.RI5_1_607500000_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1032, 392, 34, 21, -95]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-27037, 23656, 848, -864, -9562]

def zeta2 := B.equivFun.symm ![-1193171, 1499625, -194433, -337974, -1287680]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![0, -6, 2, 2, 6]], ![![0, -6, 2, 2, 6], ![70, -84, 8, 15, 69]]]
 hmul := by decide
 f := ![![![![603293701959, -271666372867, -187179085472, 37015701145, 125025767580], ![519956518513, -146660911881, -1035430269, 0, -13687557]], ![![0, 0, 0, 0, 0], ![-59139, -215, -9, 0, -1]]], ![![![1853680236162, -834722100659, -575126460365, 113734443805, 384154175041], ![1597618405270, -450630319674, -3181463058, 0, -42056388]], ![![0, 0, 0, 0, 0], ![-181710, -660, -28, 0, -3]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 3, 0, 4, 7], ![0, 0, -2, 0, 0]]], ![![![-4, 3, 0, 4, 7], ![0, 0, -2, 0, 0]], ![![-3, 22, 0, 30, 55], ![5, -7, -15, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![4, 0, 0, 0, 0], ![-24, 14, 2, 1, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![0, -6, 2, 2, 6]], ![![12, -4, 0, 0, 2], ![-4, -8, 2, 5, 15]]]
 hmul := by decide
 f := ![![![![7960615882, -3584709522, -2469880271, 488434462, 1649754102], ![6860972542, -1935231435, -13662873, 0, -180747]], ![![0, 0, 0, 0, 0], ![-3462, -294, -6, 0, 0]]], ![![![-47712169611, 21485054850, 14803295136, -2927445348, -9887846469], ![-41121427083, 11598862680, 81888804, 0, 1083312]], ![![0, 0, 0, 0, 0], ![20749, 1762, 36, 0, 0]]]]
 g := ![![![![-1165571, -1696644, 159204, 618294, 1915236], ![-147072, -328152, -2904, 0, 0]], ![![-26790878, -38997654, 3659324, 14211600, 44022042], ![-3380475, -7542629, -66747, 0, -5]]], ![![![-14218348, -20696720, 1942064, 7542333, 23363237], ![-1794072, -4003000, -35424, 0, -2]], ![![-47063771, -68507525, 6428366, 24965644, 77333913], ![-5938510, -13250203, -117255, 0, -9]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![-24, 14, 2, 1, -3]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![0, -12, 4, 4, 12]], ![![-48, 28, 4, 2, -6], ![166, -190, 12, 24, 123]]]
 hmul := by decide
 f := ![![![![-27371555954708082194, 12369251353182114566, 8446284883526064426, -1777290277385369018, -5608747117806379926], ![-23632500403412394034, 6760674923308789952, 20509206700995516, 0, 116688291571950]], ![![-1703664385354, 340731093569, -67864528375, 0, 0], ![-232678383, -527055, -333, 0, -3]]], ![![![-27371867574780219391, 12369392174807503340, 8446381042908053924, -1777310511504516794, -5608810972348823266], ![-23632769455032721338, 6760751892334985748, 20509440194498122, 0, 116689620046440]], ![![-1703683781256, 340734972729, -67865301000, 0, 0], ![-232681032, -527061, -333, 0, -3]]]]
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-8, -33, 0, -8, -3], ![8, 16, 12, 0, 0]]], ![![![-8, -13, 0, -4, -2], ![-2, 10, 6, 0, 0]], ![![-29, -206, 0, -48, -16], ![67, 84, 72, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] ![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]]
  ![![-1032, 392, 34, 21, -95]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![0, -12, 4, 4, 12]], ![![12, -4, 0, 0, 2], ![-4, -8, 2, 5, 15]]]
 hmul := by decide
 f := ![![![![953084725213204, -430700499856980, -294101751776143, 61885675830229, 195297971454412], ![822889668994133, -235408426461957, -714133308938, 0, -4063855586]], ![![-320274724, 33054629, 39206943, 0, 0], ![4356327, 390684, 1548, 0, 0]]]]
 g := ![![![![-22, 23, -13, -1, -2]], ![![-141, 214, 0, -17, -225]]], ![![![-10, 16, 8, -10, -32]], ![![-130, 119, -59, -52, -33]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1237, -12952, -15792, -1268, 39958])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![10676839, -4412835, -348407, -177106, 1177610])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, -3, 1, 1, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![-24, 14, 2, 1, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![6, -2, 0, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
