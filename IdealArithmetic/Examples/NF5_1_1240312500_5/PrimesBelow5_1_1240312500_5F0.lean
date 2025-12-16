
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Examples.NF5_1_1240312500_5.RI5_1_1240312500_5
import IdealArithmetic.ClassGroupGeneration

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate O ℤ timesTableO I2N0
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![15, -70, -41, -51, 126], ![3, -27, -16, -20, 51]]]
  hmulB := by decide
  f := ![![![64, -246, 0, -224, 555], ![-122, -360, 0, -8, -2]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![8, -28, 0, -25, 63], ![-14, -41, 0, -1, 0]], ![![32, -123, 0, -112, 278], ![-61, -180, 0, -4, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 1, 0, 2, 0], ![-30, -70, -41, -51, 126], ![-14, -27, -16, -20, 51]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-11, -7, -4, -5, 13]] i)))

def SI2N1: IdealEqSpanCertificate O ℤ timesTableO I2N1
 ![![2, 0, 0, 0, 0], ![-11, -7, -4, -5, 13]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-11, -7, -4, -5, 13], ![-36, -16, -10, -13, 33], ![-96, -27, -11, -17, 45], ![-42, -58, -20, -21, 60], ![-68, -42, -18, -22, 59]]]
  hmulB := by decide
  f := ![![![535, -247, -77, -53, 201], ![-444, 160, 2, 0, 0]], ![![13, 5, 3, 4, -10], ![-1, 1, 0, 0, 0]], ![![273, -120, -36, -24, 94], ![-221, 80, 1, 0, 0]], ![![-4142, 1950, 610, 424, -1595], ![3454, -1244, -16, 1, 0]], ![![4157, -1937, -603, -415, 1573], ![-3448, 1243, 16, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, -7, -4, -5, 13], ![-5, -16, -10, -13, 33], ![-29, -27, -11, -17, 45], ![18, -58, -20, -21, 60], ![-4, -42, -18, -22, 59]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-4, -2, -1, -2, 5]] i)))

def SI2N2: IdealEqSpanCertificate O ℤ timesTableO I2N2
 ![![2, 0, 0, 0, 0], ![-4, -2, -1, -2, 5]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-4, -2, -1, -2, 5], ![-15, 0, 0, 0, 3], ![9, -96, -48, -60, 153], ![-213, 15, -42, -48, 120], ![-94, -26, -32, -39, 100]]]
  hmulB := by decide
  f := ![![![12, -2, -1, -2, 2], ![-2, 2, 0, 0, 0]], ![![-1048, 332, 141, 300, -432], ![324, -212, 0, -1, 0]], ![![6, -1, 0, -1, 1], ![-1, 1, 0, 0, 0]], ![![-26964, 8502, 3617, 7690, -11059], ![8294, -5444, 0, -26, 1]], ![![8, 0, 0, 0, -1], ![0, 1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![-3, -2, -1, -2, 5], ![-9, 0, 0, 0, 3], ![0, -96, -48, -60, 153], ![-153, 15, -42, -48, 120], ![-68, -26, -32, -39, 100]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulEqCertificate O ℤ timesTableO (I2N0) I2N1
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![-11, -7, -4, -5, 13]]
  ![![2, 0, 0, 0, 0], ![-10, -6, -4, -5, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-22, -14, -8, -10, 26]], ![![0, 2, 0, 0, 0], ![-36, -16, -10, -13, 33]]]
 hmul := by decide
 f :=  ![![![![-19476609770, 9348080758, 2755056444, 1859634070, -7291011229], ![16852300070, -6162269490, -26151801, 561855, 0]], ![![182401, 0, 0, 0, 0], ![7546, 424, 0, 2, 0]]], ![![![97659270082, -46872980144, -13814354979, -9324544047, 36558458715], ![-84500503072, 30898742001, 131129895, -2817243, 0]], ![![-914589, 0, 0, 0, 0], ![-37837, -2126, 0, -10, 0]]]]
 g :=  ![![![![1872, -344, -534, -230, 800], ![-1480, 512, 0, 4, 0]], ![![-10338, 1906, 2954, 1274, -4429], ![8182, -2830, 0, -22, 0]]], ![![![16, 4, 1, 3, -7], ![-4, 2, 0, 0, 0]], ![![-16891, 3115, 4827, 2082, -7238], ![13369, -4624, 0, -36, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1) I2N2
  ![![2, 0, 0, 0, 0], ![-10, -6, -4, -5, 13]] ![![2, 0, 0, 0, 0], ![-4, -2, -1, -2, 5]]
  ![![-39, -18, -9, -11, 28]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-8, -4, -2, -4, 10]], ![![-20, -12, -8, -10, 26], ![-63, -9, -4, -7, 20]]]
 hmul := by decide
 f :=  ![![![![9857919693823, -2970554194735, -1405650104399, -2868979443750, 4091085058280], ![-2945768051236, 2054276842995, 0, 3232975239, -40820250]], ![![-2708079, 0, 0, 0, 0], ![-18561, 0, 0, -21, 0]]]]
 g :=  ![![![![-10, 12, 4, 6, -14]], ![![-33, 45, 7, 19, -41]]], ![![![16, -13, 1, -2, 4]], ![![95, -131, -54, -76, 177]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N2 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N2) I2N2
  ![![-39, -18, -9, -11, 28]] ![![2, 0, 0, 0, 0], ![-4, -2, -1, -2, 5]]
  ![![2, 0, 0, 0, 0], ![-8, -5, -3, -4, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![-78, -36, -18, -22, 56], ![56, 49, 37, 54, -146]]]
 hmul := by decide
 f :=  ![![![![-928953968, 273768916, 136270530, 272987569, -387773310], ![273582922, -196463739, 0, -24804, -3]]], ![![![4645893313, -1369175657, -681517450, -1365267988, 1939335501], ![-1368245485, 982556301, 0, 124050, 15]]]]
 g :=  ![![![![-7, 2, 3, 5, -12], ![8, 0, 0, 0, 0]], ![![-16, -3, 2, 5, -18], ![-11, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N3 : IdealMulEqCertificate O ℤ timesTableO (I2N0*I2N1*I2N2*I2N2) I2N2
  ![![2, 0, 0, 0, 0], ![-8, -5, -3, -4, 10]] ![![2, 0, 0, 0, 0], ![-4, -2, -1, -2, 5]]
  ![![2, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N2
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-8, -4, -2, -4, 10]], ![![-16, -10, -6, -8, 20], ![-8, -16, 0, -2, 6]]]
 hmul := by decide
 f :=  ![![![![-2361005, 711466, 336656, 687133, -979831], ![705532, -492009, 0, -774, 9]], ![![0, 0, 0, 0, 0], ![3, 0, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0, 0]], ![![-4, -2, -1, -2, 5]]], ![![![-8, -5, -3, -4, 10]], ![![-4, -8, 0, -1, 3]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : PrimesBelowPCertificate 2 ![I2N0, I2N1, I2N2, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI2N3, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate O ℤ timesTableO I3N0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![15, -70, -41, -51, 126], ![3, -27, -16, -20, 51]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![5, -70, -41, -51, 42], ![1, -27, -16, -20, 17]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N0)

def MemCI3N0 : IdealMemCertificate O ℤ B I3N0
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] ![2544, -68673, -42899, -49268, 124656] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI3N0
 g := ![848, -68673, -42899, -49268, 41552]
 hmem := by decide

def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]],![[1, 2]]]
 h' := ![![[2, 2], [0, 1]],![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : PrimeIdeal O 3 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N0
  hcard := NI3N0
  P := [2, 1, 1]
  f := ofList [2, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  hneq := by decide
  hlen := by decide
  c := ![2544, -68673, -42899, -49268, 124656]
  a := ![-37, 170, 100, 121, -311]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI3N0
  hpmem := by 
    show  _ ∈ I3N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := PrimeIdeal_isPrime PI3N0
def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate O ℤ timesTableO I3N1
 ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![15, -70, -41, -52, 126], ![3, -27, -16, -20, 50]]]
  hmulB := by decide
  f := ![![![-15, -6, 102, -20, -100], ![-30, -120, 90, 0, 6]], ![![-15, -5, 101, -22, -100], ![-29, -114, 93, 0, 6]], ![![-6, -3, 50, -10, -50], ![-11, -56, 45, 0, 3]], ![![0, 0, 0, -1, 0], ![0, 2, 2, 0, 0]], ![![-3, -4, 34, -8, -33], ![-4, -38, 32, 0, 2]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![37, -70, -41, -52, 126], ![13, -27, -16, -20, 50]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulEqCertificate O ℤ timesTableO (I3N0) I3N1
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![6, 9, 6, 7, -18]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, -1, 1, 0, 0]]]
 hmul := by decide
 f :=  ![![![![62, 919, -1343, 2735, 448], ![103, -774, -4376, 0, -27]], ![![13, 0, 0, 0, 0], ![5, 14, 0, 0, 0]]]]
 g :=  ![![![![-654, 792, 195, 357, -810]], ![![1193, -1457, -360, -658, 1494]]], ![![![975, -1193, -295, -539, 1224]], ![![-1796, 2185, 539, 986, -2238]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate O ℤ timesTableO (I3N0*I3N1) I3N1
  ![![6, 9, 6, 7, -18]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-15, -10, -5, -7, 18]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![18, 27, 18, 21, -54], ![45, -1, 4, 8, -18]]]
 hmul := by decide
 f :=  ![![![![156, 2206, -2325, 45, -90], ![686, 7032, -8, 0, 0]]], ![![![-4514682, -45142960, 49658480, -112217, -1276], ![-13542759, -148805208, 169120, 0, 48]]]]
 g :=  ![![![![6, 9, 6, 7, -18], ![0, 0, 0, 0, 0]], ![![5, -7, -2, -2, 6], ![-2, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N2 : IdealMulEqCertificate O ℤ timesTableO (I3N0*I3N1*I3N1) I3N1
  ![![3, 0, 0, 0, 0], ![-15, -10, -5, -7, 18]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N1
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-45, -30, -15, -21, 54], ![-36, -6, -6, -6, 18]]]
 hmul := by decide
 f :=  ![![![![-386, -7148, 10377, -21080, -3516], ![-625, 5973, 33728, 0, 210]], ![![0, 0, 0, 0, 0], ![8, 0, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-15, -10, -5, -7, 18]], ![![-12, -2, -2, -2, 6]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : PrimesBelowPCertificate 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI3N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![340, 92, 11, -11, 52]] i)))

def SI5N0: IdealEqSpanCertificate O ℤ timesTableO I5N0
 ![![340, 92, 11, -11, 52]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![340, 92, 11, -11, 52], ![-9, -283, -289, -457, 1266], ![-3057, -2490, -1802, -2591, 6984], ![-8952, -5887, -3857, -5343, 14226], ![-4961, -3543, -2424, -3415, 9143]]]
  hmulB := by decide
  f := ![![![-1003556, 1222813, 301870, 551995, -1253072]], ![![101297, -123428, -30470, -55717, 126482]], ![![-4875721, 5940967, 1466617, 2681835, -6087976]], ![![8721444, -10626905, -2623411, -4797133, 10889868]], ![![1616353, -1969494, -486199, -889057, 2018229]]]
  g := ![![![-56, 92, 11, -11, 52], ![-557, -283, -289, -457, 1266], ![-2765, -2490, -1802, -2591, 6984], ![-5376, -5887, -3857, -5343, 14226], ![-3533, -3543, -2424, -3415, 9143]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulEqCertificate O ℤ timesTableO (I5N0) I5N0
  ![![340, 92, 11, -11, 52]] ![![340, 92, 11, -11, 52]]
  ![![-78355, -141625, -126291, -193092, 529926]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-78355, -141625, -126291, -193092, 529926]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N1 : IdealMulEqCertificate O ℤ timesTableO (I5N0*I5N0) I5N0
  ![![-78355, -141625, -126291, -193092, 529926]] ![![340, 92, 11, -11, 52]]
  ![![-539697790, -393459409, -272140678, -385202223, 1032798572]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N0
 hI2 := rfl
 M :=  ![![![-539697790, -393459409, -272140678, -385202223, 1032798572]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N2 : IdealMulEqCertificate O ℤ timesTableO (I5N0*I5N0*I5N0) I5N0
  ![![-539697790, -393459409, -272140678, -385202223, 1032798572]] ![![340, 92, 11, -11, 52]]
  ![![-1023405476669, -652192749508, -419608169150, -578007523590, 1536176127372]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N1
 hI2 := rfl
 M :=  ![![![-1023405476669, -652192749508, -419608169150, -578007523590, 1536176127372]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N3 : IdealMulEqCertificate O ℤ timesTableO (I5N0*I5N0*I5N0*I5N0) I5N0
  ![![-1023405476669, -652192749508, -419608169150, -578007523590, 1536176127372]] ![![340, 92, 11, -11, 52]]
  ![![5, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N2
 hI2 := rfl
 M :=  ![![![-1505992370945150, -904700142463950, -560955749090345, -761232963397845, 2013086742963340]]]
 hmul := by decide
 f :=  ![![![![-11849859472873035250340686016282, 14438815188775640172983470710515, 3564439493226710351387837036094, 6517882751529705612761239858449, -14796105520329829597375848276908]]]]
 g :=  ![![![![-301198474189030, -180940028492790, -112191149818069, -152246592679569, 402617348592668]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : PrimesBelowPCertificate 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI5N3, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-12, -4, -4, -5, 13]] i)))

def SI7N0: IdealEqSpanCertificate O ℤ timesTableO I7N0
 ![![7, 0, 0, 0, 0], ![-12, -4, -4, -5, 13]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 6, 1, 0, 0], ![5, 5, 0, 1, 0], ![3, 4, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-12, -4, -4, -5, 13], ![-36, -17, -7, -13, 33], ![-96, -24, -12, -11, 45], ![3, -268, -143, -175, 438], ![-59, -123, -66, -82, 211]]]
  hmulB := by decide
  f := ![![![30700, 34458, -12645, 3990, -6627], ![-80241, 32613, 0, 0, 63]], ![![61182, 68680, -25197, 7956, -13218], ![-159915, 64995, 0, 0, 126]], ![![64137, 71999, -26418, 8338, -13850], ![-167653, 68139, 0, 0, 132]], ![![65630, 73670, -27030, 8533, -14175], ![-171540, 69720, 0, 0, 135]], ![![48120, 54014, -19817, 6257, -10395], ![-125768, 51117, 0, 0, 99]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -6, 7, 0, 0], ![-5, -5, 0, 7, 0], ![-3, -4, 0, 0, 7]], ![![-2, -1, -4, -5, 13], ![-7, -6, -7, -13, 33], ![-20, -11, -12, -11, 45], ![-1, -41, -143, -175, 438], ![-12, -23, -66, -82, 211]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0)

def MemCI7N0 : IdealMemCertificate O ℤ B I7N0
  ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 6, 1, 0, 0], ![5, 5, 0, 1, 0], ![3, 4, 0, 0, 1]] ![7015, -315622, -196112, -249022, 596736] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI7N0
 g := ![7179, -40112, -196112, -249022, 596736]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]],![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]],![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : PrimeIdeal O 7 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [2, 2, 1]
  f := ofList [2, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![7015, -315622, -196112, -249022, 596736]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI7N0
  hpmem := by 
    show  _ ∈ I7N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := PrimeIdeal_isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-9, -7, -4, -5, 13]] i)))

def SI7N1: IdealEqSpanCertificate O ℤ timesTableO I7N1
 ![![7, 0, 0, 0, 0], ![-9, -7, -4, -5, 13]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-9, -7, -4, -5, 13], ![-36, -14, -10, -13, 33], ![-96, -27, -9, -17, 45], ![-42, -58, -20, -19, 60], ![-68, -42, -18, -22, 61]]]
  hmulB := by decide
  f := ![![![3984526, -906633, 33880, 191499, -274487], ![-4882213, 1966622, 10584, 0, 252]], ![![3415679, -777194, 29045, 164162, -235306], ![-4185200, 1685857, 9073, 0, 216]], ![![1707654, -388555, 14521, 82072, -117640], ![-2092373, 842837, 4536, 0, 108]], ![![2182009, -496485, 18556, 104872, -150323], ![-2673589, 1076960, 5796, 0, 138]], ![![2846090, -647595, 24200, 136785, -196062], ![-3487295, 1404730, 7560, 0, 180]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 7, 0, 0, 0], ![-3, 0, 7, 0, 0], ![-4, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![-1, -7, -4, -5, 13], ![-7, -14, -10, -13, 33], ![-13, -27, -9, -17, 45], ![12, -58, -20, -19, 60], ![-3, -42, -18, -22, 61]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulEqCertificate O ℤ timesTableO (I7N0) I7N1
  ![![7, 0, 0, 0, 0], ![-12, -4, -4, -5, 13]] ![![7, 0, 0, 0, 0], ![-9, -7, -4, -5, 13]]
  ![![-2702, 1718, 751, 583, -1704]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0, 0], ![-63, -49, -28, -35, 91]], ![![-84, -28, -28, -35, 91], ![-38, -8, -10, -11, 25]]]
 hmul := by decide
 f :=  ![![![![-4185756817838115202, 952424567353176374, -35589374654982233, -201168416032899798, 288344348940874429], ![5128787929155228276, -2065944457703522747, -11118611598751602, 0, -264723076156560]], ![![-60590143794, 0, 0, 0, 0], ![-35730292, 0, 0, 0, 45684]]]]
 g :=  ![![![![102718, 58107, 34566, 46081, -121128]], ![![-4764, -7304, -6336, -9618, 26341]]], ![![![91713, 45823, 24636, 31302, -80885]], ![![-93515, -52433, -30988, -41192, 108169]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N1 : IdealMulEqCertificate O ℤ timesTableO (I7N0*I7N1) I7N1
  ![![-2702, 1718, 751, 583, -1704]] ![![7, 0, 0, 0, 0], ![-9, -7, -4, -5, 13]]
  ![![7, 0, 0, 0, 0], ![13, 8, 3, 5, -14]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N0
 hI2 := rfl
 M :=  ![![![-18914, 12026, 5257, 4081, -11928], ![-18240, 12339, 5881, 4820, -13601]]]
 hmul := by decide
 f :=  ![![![![-1478871829566272, 341235946044361, -18075057546082, -75860610707041, 112010769424590], ![1832705447146494, -745734691657372, -30537872, 0, 60]]], ![![![-2440138576900109, 563039324382299, -29823845661326, -125170010647771, 184817773952549], ![3023964059813198, -1230462270538904, -50387490, 0, 99]]]]
 g :=  ![![![![-2897, 1598, 706, 508, -1494], ![105, 0, 0, 0, 0]], ![![-2953, 1549, 760, 555, -1569], ![187, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI7N2 : IdealMulEqCertificate O ℤ timesTableO (I7N0*I7N1*I7N1) I7N1
  ![![7, 0, 0, 0, 0], ![13, 8, 3, 5, -14]] ![![7, 0, 0, 0, 0], ![-9, -7, -4, -5, 13]]
  ![![7, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N1
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0, 0], ![-63, -49, -28, -35, 91]], ![![91, 56, 21, 35, -98], ![49, 14, -7, -7, 14]]]
 hmul := by decide
 f :=  ![![![![255012247, -58025322, 2168242, 12255948, -17567042], ![-312465274, 125865200, 677388, 0, 16128]], ![![0, 0, 0, 0, 0], ![-6, 0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0, 0]], ![![-9, -7, -4, -5, 13]]], ![![![13, 8, 3, 5, -14]], ![![7, 2, -1, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : PrimesBelowPCertificate 7 ![I7N0, I7N1, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI7N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate O ℤ timesTableO I11N0
 ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0)

def MemCI11N0 : IdealMemCertificate O ℤ B I11N0
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] ![145830702594654, 9644281011200, -8482425736136, 43613466727424, -63345789815616] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI11N0
 g := ![13257336599514, 876752819200, -771129612376, 3964860611584, -5758708165056]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [2, 1, 8, 10, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 7, 9, 3, 9], [8, 2, 2, 4, 1], [6, 7, 4, 10, 1], [1, 5, 7, 5], [0, 1]]
 g := ![![[6, 1, 6, 0, 9], [1], []],![[8, 8, 2, 6, 7, 7, 4, 1], [8, 6, 2, 4, 3, 4, 1, 1], [2, 10, 0, 4]],![[0, 6, 7, 3, 4, 9, 2, 9], [9, 2, 4, 6, 8, 9, 9, 3], [9, 10, 0, 1]],![[10, 7, 1, 3, 10, 6, 6, 5], [0, 6, 3, 7, 8, 9], [5, 2, 1, 1]],![[7, 10, 4, 1, 9], [7, 1, 0, 8, 4, 6, 9], [2, 3]]]
 h' := ![![[10, 7, 9, 3, 9], [9, 10, 3, 1, 3], [0, 0, 1], [0, 1]],![[8, 2, 2, 4, 1], [8, 3, 0, 6, 7], [8, 8, 5, 1, 7], [10, 7, 9, 3, 9]],![[6, 7, 4, 10, 1], [3, 3, 2, 1, 8], [2, 3, 9, 10, 6], [8, 2, 2, 4, 1]],![[1, 5, 7, 5], [8, 4, 0, 5, 4], [4, 9, 9, 8], [6, 7, 4, 10, 1]],![[0, 1], [6, 2, 6, 9], [8, 2, 9, 3, 9], [1, 5, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 8, 9, 6], [], [], []]
 b := ![[], [6, 6, 1, 0, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : PrimeIdeal O 11 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [2, 1, 8, 10, 8, 1]
  f := ofList [2, 1, 8, 10, 8, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![145830702594654, 9644281011200, -8482425736136, 43613466727424, -63345789815616]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI11N0
  hpmem := by 
    show  _ ∈ I11N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := PrimeIdeal_isPrime PI11N0
def PBC11 : PrimesBelowPCertificate 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I11N
    unfold I11N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3556, -1949, -1132, -1493, 3910]] i)))

def SI13N0: IdealEqSpanCertificate O ℤ timesTableO I13N0
 ![![-3556, -1949, -1132, -1493, 3910]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![7, 2, 10, 1, 0], ![7, 1, 7, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-3556, -1949, -1132, -1493, 3910], ![-10665, -5748, -3296, -4321, 11292], ![-30939, -16375, -9259, -12061, 31446], ![-37956, -19611, -10857, -14003, 36384], ![-31733, -16632, -9323, -12095, 31491]]]
  hmulB := by decide
  f := ![![![-10584, 12896, 3183, 5821, -13214]], ![![47673, -58093, -14341, -26225, 59532]], ![![-214779, 261718, 64620, 118153, -268218]], ![![-128196, 156217, 38572, 70526, -160100]], ![![-107867, 131442, 32454, 59340, -134707]]]
  g := ![![![-1575, -221, -1044, -1493, 3910], ![-4574, -646, -3010, -4321, 11292], ![-12818, -1823, -8367, -12061, 31446], ![-14971, -2153, -9655, -14003, 36384], ![-12885, -1841, -8370, -12095, 31491]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N0)

def MemCI13N0 : IdealMemCertificate O ℤ B I13N0
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![7, 2, 10, 1, 0], ![7, 1, 7, 0, 1]] ![38247878, 198364858, 134997530, 187229124, -425704440] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI13N0
 g := ![131351930, 19200850, 95587490, 187229124, -425704440]
 hmem := by decide

def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 9, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3], [7, 9], [0, 1]]
 g := ![![[9, 9, 1], [4, 1], [1]],![[1, 5, 9], [9, 3], [1]],![[4, 12, 3], [11, 9], [1]]]
 h' := ![![[5, 3], [12, 8, 12], [2, 4, 12], [0, 1]],![[7, 9], [1, 7, 4], [10, 8, 4], [5, 3]],![[0, 1], [6, 11, 10], [7, 1, 10], [7, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [7, 3, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : PrimeIdeal O 13 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N0
  hcard := NI13N0
  P := [11, 9, 1, 1]
  f := ofList [11, 9, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
  hneq := by decide
  hlen := by decide
  c := ![38247878, 198364858, 134997530, 187229124, -425704440]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI13N0
  hpmem := by 
    show  _ ∈ I13N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := PrimeIdeal_isPrime PI13N0
def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10584, 12896, 3183, 5821, -13214]] i)))

def SI13N1: IdealEqSpanCertificate O ℤ timesTableO I13N1
 ![![-10584, 12896, 3183, 5821, -13214]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 6, 1, 0, 0], ![5, 12, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-10584, 12896, 3183, 5821, -13214], ![47673, -58093, -14341, -26225, 59532], ![-214779, 261718, 64620, 118153, -268218], ![459984, -560445, -138363, -252989, 574314], ![127597, -155459, -38378, -70173, 159301]]]
  hmulB := by decide
  f := ![![![-3556, -1949, -1132, -1493, 3910]], ![![-10665, -5748, -3296, -4321, 11292]], ![![-9217, -4962, -2843, -3726, 9736]], ![![-14132, -7564, -4313, -5640, 14726]], ![![-7090, -3790, -2159, -2822, 7367]]]
  g := ![![![-2734, -768, 3183, 5821, -13214], ![12317, 3461, -14341, -26225, 59532], ![-55496, -15596, 64620, 118153, -268218], ![118834, 33387, -138363, -252989, 574314], ![32962, 9260, -38378, -70173, 159301]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N1)

def MemCI13N1 : IdealMemCertificate O ℤ B I13N1
  ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![7, 6, 1, 0, 0], ![5, 12, 0, 1, 0], ![2, 5, 0, 0, 1]] ![368937, -13724027, -8640976, -9979915, 25153335] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI13N1
 g := ![4649898, 2470318, -8640976, -9979915, 25153335]
 hmem := by decide

def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [12], [0, 1]],![[], [12], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 8], [0, 1]],![[0, 1], [5], [0, 5], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : PrimeIdeal O 13 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N1
  hcard := NI13N1
  P := [5, 0, 1]
  f := ofList [5, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  hneq := by decide
  hlen := by decide
  c := ![368937, -13724027, -8640976, -9979915, 25153335]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI13N1
  hpmem := by 
    show  _ ∈ I13N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI13N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := PrimeIdeal_isPrime PI13N1
def MulI13N0 : IdealMulEqCertificate O ℤ timesTableO (I13N0) I13N1
  ![![-3556, -1949, -1132, -1493, 3910]] ![![-10584, 12896, 3183, 5821, -13214]]
  ![![13, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![13, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC13 : PrimesBelowPCertificate 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI13N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![72, 43, 21, 28, -74]] i)))

def SI17N0: IdealEqSpanCertificate O ℤ timesTableO I17N0
 ![![17, 0, 0, 0, 0], ![72, 43, 21, 28, -74]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![5, 7, 5, 1, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![72, 43, 21, 28, -74], ![198, 131, 79, 94, -246], ![672, 339, 213, 284, -702], ![978, -86, -76, -56, 114], ![712, 157, 83, 122, -320]]]
  hmulB := by decide
  f := ![![![-71, -43, -21, -28, 74], ![17, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-59, -35, -17, -23, 61], ![14, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-5, -7, -5, -1, 17]], ![![26, 33, 23, 6, -74], ![84, 109, 77, 20, -246], ![246, 309, 219, 58, -702], ![24, -52, -38, -10, 114], ![136, 141, 99, 26, -320]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0)

def MemCI17N0 : IdealMemCertificate O ℤ B I17N0
  ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![5, 7, 5, 1, 1]] ![-106258226547, -91939487940, -64382425356, -117681238272, 245845883304] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI17N0
 g := ![-78558096651, -106638863004, -76094814228, -21383948328, 245845883304]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [6, 4, 6, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 12, 16], [1, 2, 2, 14], [4, 9, 3, 4], [0, 1]]
 g := ![![[0, 16, 1, 16], [1, 14, 8], [1], []],![[14, 14, 1, 16, 0, 15], [13, 5, 2], [2, 4, 16], [16, 15, 1]],![[2, 3, 4, 3, 12, 3], [5, 9, 1], [16, 8, 2], [1, 16, 9]],![[5, 6, 13, 11, 0, 8], [12, 2, 8], [5, 8, 4], [12, 2, 16]]]
 h' := ![![[0, 5, 12, 16], [13, 11, 12, 13], [11, 13, 11, 5], [0, 0, 1], [0, 1]],![[1, 2, 2, 14], [5, 16, 4, 6], [7, 7, 1, 6], [6, 16, 16, 4], [0, 5, 12, 16]],![[4, 9, 3, 4], [13, 6, 5, 4], [14, 15, 2, 1], [12, 6, 3, 11], [1, 2, 2, 14]],![[0, 1], [4, 1, 13, 11], [12, 16, 3, 5], [12, 12, 14, 2], [4, 9, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 6, 5], []]
 b := ![[], [], [3, 2, 8, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : PrimeIdeal O 17 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [6, 4, 6, 12, 1]
  f := ofList [6, 4, 6, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![-106258226547, -91939487940, -64382425356, -117681238272, 245845883304]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI17N0
  hpmem := by 
    show  _ ∈ I17N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := PrimeIdeal_isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate O ℤ timesTableO I17N1
 ![![17, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-7, 1, 0, 0, 0], ![0, -7, 1, 0, 0], ![0, 1, -7, 2, 0], ![15, -70, -41, -58, 126], ![3, -27, -16, -20, 44]]]
  hmulB := by decide
  f := ![![![-225566, 136112, -997445, 288558, -3402], ![-546822, -100640, -2439432, 459, 0]], ![![-150384, 90747, -664964, 192372, -2268], ![-364564, -67082, -1626288, 306, 0]], ![![-50116, 30242, -221599, 64108, -756], ![-121492, -22354, -541960, 102, 0]], ![![-25060, 15127, -110831, 32063, -378], ![-60751, -11174, -271056, 51, 0]], ![![-119414, 72065, -528060, 152766, -1801], ![-289486, -53265, -1291464, 243, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 17, 0, 0, 0], ![-2, 0, 17, 0, 0], ![-2, 0, 0, 17, 0], ![-9, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -7, 1, 0, 0], ![0, 1, -7, 2, 0], ![-13, -70, -41, -58, 126], ![-3, -27, -16, -20, 44]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulEqCertificate O ℤ timesTableO (I17N0) I17N1
  ![![17, 0, 0, 0, 0], ![72, 43, 21, 28, -74]] ![![17, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]]
  ![![17, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0, 0], ![-119, 17, 0, 0, 0]], ![![1224, 731, 357, 476, -1258], ![-306, -170, -68, -102, 272]]]
 hmul := by decide
 f :=  ![![![![-30397658, 18340045, -134392232, 38879350, -458486], ![-73690490, -13560071, -328680600, 61851, 0]], ![![-14, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0, 0]], ![![-7, 1, 0, 0, 0]]], ![![![72, 43, 21, 28, -74]], ![![-18, -10, -4, -6, 16]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : PrimesBelowPCertificate 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI17N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate O ℤ timesTableO I19N0
 ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0)

def MemCI19N0 : IdealMemCertificate O ℤ B I19N0
  ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] ![145937419711081, 9738604949712, -8416420808826, 43733397930162, -63596751854076] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI19N0
 g := ![7680916826899, 512558155248, -442969516254, 2301757785798, -3347197466004]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [11, 1, 1, 10, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 14, 3, 8, 5], [0, 13, 15, 3, 11], [16, 4, 0, 7, 2], [17, 6, 1, 1, 1], [0, 1]]
 g := ![![[14, 5, 4, 17, 5], [18, 5, 1, 12, 1], [], []],![[6, 8, 8, 1, 9, 3, 12, 9], [11, 2, 7, 15, 11, 5, 11, 1], [13, 13, 13, 11], [1, 15, 0, 6]],![[2, 10, 8, 3, 11, 18, 12, 1], [16, 16, 5, 1, 5, 1], [15, 12, 11, 6], [4, 17, 17, 7]],![[18, 5, 5, 16, 1, 13, 2, 18], [3, 10, 14, 7, 4, 3, 12, 12], [16, 17, 14, 9], [6, 9, 0, 4]],![[5, 3, 17, 2, 12, 18, 3, 7], [7, 12, 9, 0, 5, 10, 14, 4], [17, 5, 7, 1], [0, 9, 14, 1]]]
 h' := ![![[17, 14, 3, 8, 5], [11, 3, 4, 5, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[0, 13, 15, 3, 11], [10, 10, 14, 14, 13], [1, 7, 4, 5, 2], [12, 6, 16, 18, 12], [17, 14, 3, 8, 5]],![[16, 4, 0, 7, 2], [14, 16, 2, 11, 8], [4, 17, 17, 11], [13, 18, 18, 11, 5], [0, 13, 15, 3, 11]],![[17, 6, 1, 1, 1], [6, 15, 17, 12, 16], [14, 6, 0, 3, 14], [0, 4, 1, 16, 3], [16, 4, 0, 7, 2]],![[0, 1], [18, 13, 1, 15, 11], [0, 8, 17, 0, 2], [4, 10, 2, 12, 18], [17, 6, 1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 4, 11, 4], [], [], []]
 b := ![[], [13, 11, 1, 14, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : PrimeIdeal O 19 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [11, 1, 1, 10, 7, 1]
  f := ofList [11, 1, 1, 10, 7, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![145937419711081, 9738604949712, -8416420808826, 43733397930162, -63596751854076]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI19N0
  hpmem := by 
    show  _ ∈ I19N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := PrimeIdeal_isPrime PI19N0
def PBC19 : PrimesBelowPCertificate 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I19N
    unfold I19N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-107, -64, -42, -53, 138]] i)))

def SI23N0: IdealEqSpanCertificate O ℤ timesTableO I23N0
 ![![23, 0, 0, 0, 0], ![-107, -64, -42, -53, 138]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![12, 19, 6, 1, 0], ![0, 2, 13, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-107, -64, -42, -53, 138], ![-381, -165, -99, -141, 360], ![-1035, -330, -144, -207, 594], ![-471, -1281, -624, -735, 1926], ![-768, -723, -365, -455, 1201]]]
  hmulB := by decide
  f := ![![![15125, -3217, -3921, -1814, 6114], ![-12719, 4485, 0, 0, 0]], ![![-994, 224, 267, 128, -426], ![851, -299, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![7126, -1460, -1803, -813, 2766], ![-5921, 2093, 0, 0, 0]], ![![-12, 64, 53, 48, -133], ![90, -26, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-12, -19, -6, 23, 0], ![0, -2, -13, 0, 23]], ![![23, 29, -66, -53, 138], ![57, 78, -171, -141, 360], ![63, 105, -288, -207, 594], ![363, 384, -924, -735, 1926], ![204, 240, -576, -455, 1201]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0)

def MemCI23N0 : IdealMemCertificate O ℤ B I23N0
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![12, 19, 6, 1, 0], ![0, 2, 13, 0, 1]] ![38377768, 192666677, 131457667, 182734430, -414932490] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N0
 g := ![-93671104, -106496631, 192572759, 182734430, -414932490]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [12, 2, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 19, 7], [10, 3, 16], [0, 1]]
 g := ![![[12, 10, 9], [10, 11, 8], [14, 4, 1], []],![[1, 10, 14, 22], [6, 0, 20, 10], [6, 5, 0, 17], [2, 3]],![[0, 21, 18, 6], [15, 0, 22, 6], [16, 2, 3, 3], [16, 3]]]
 h' := ![![[17, 19, 7], [18, 12, 20], [16, 16, 13], [0, 0, 1], [0, 1]],![[10, 3, 16], [2, 20, 6], [7, 17, 13], [12, 8, 3], [17, 19, 7]],![[0, 1], [0, 14, 20], [15, 13, 20], [0, 15, 19], [10, 3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [4, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : PrimeIdeal O 23 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N0
  hcard := NI23N0
  P := [12, 2, 19, 1]
  f := ofList [12, 2, 19, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![38377768, 192666677, 131457667, 182734430, -414932490]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI23N0
  hpmem := by 
    show  _ ∈ I23N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := PrimeIdeal_isPrime PI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-6, -12, -4, -5, 13]] i)))

def SI23N1: IdealEqSpanCertificate O ℤ timesTableO I23N1
 ![![23, 0, 0, 0, 0], ![-6, -12, -4, -5, 13]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![15, 11, 1, 0, 0], ![21, 5, 0, 1, 0], ![14, 15, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-6, -12, -4, -5, 13], ![-36, -11, -15, -13, 33], ![-96, -32, -6, -27, 45], ![-117, 292, 185, 239, -570], ![-83, 93, 62, 78, -191]]]
  hmulB := by decide
  f := ![![![290947, -7274, 106350, 78093, -194853], ![-217695, 220938, 460, 0, 0]], ![![5524410, -138196, 2019327, 1482786, -3699750], ![-4133721, 4195131, 8740, 0, 0]], ![![2819217, -70518, 1030504, 756697, -1888061], ![-2109506, 2140857, 4460, 0, 0]], ![![1466607, -36682, 536087, 393648, -982205], ![-1097396, 1113711, 2320, 0, 0]], ![![3779974, -94556, 1381687, 1014569, -2531486], ![-2828416, 2870439, 5980, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-15, -11, 23, 0, 0], ![-21, -5, 0, 23, 0], ![-14, -15, 0, 0, 23]], ![![-1, -6, -4, -5, 13], ![0, -12, -15, -13, 33], ![-3, -22, -6, -27, 45], ![3, 244, 185, 239, -570], ![1, 82, 62, 78, -191]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1)

def MemCI23N1 : IdealMemCertificate O ℤ B I23N1
  ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![15, 11, 1, 0, 0], ![21, 5, 0, 1, 0], ![14, 15, 0, 0, 1]] ![367894, -13719203, -8638134, -9976469, 25144497] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI23N1
 g := ![-546835, -10694993, -8638134, -9976469, 25144497]
 hmem := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [14, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22], [0, 1]]
 g := ![![[10, 12], [12, 4], [2, 4], [1]],![[9, 11], [4, 19], [17, 19], [1]]]
 h' := ![![[21, 22], [16, 14], [18, 21], [9, 21], [0, 1]],![[0, 1], [11, 9], [22, 2], [13, 2], [21, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : PrimeIdeal O 23 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N1
  hcard := NI23N1
  P := [14, 2, 1]
  f := ofList [14, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
  hneq := by decide
  hlen := by decide
  c := ![367894, -13719203, -8638134, -9976469, 25144497]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI23N1
  hpmem := by 
    show  _ ∈ I23N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI23N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := PrimeIdeal_isPrime PI23N1
def MulI23N0 : IdealMulEqCertificate O ℤ timesTableO (I23N0) I23N1
  ![![23, 0, 0, 0, 0], ![-107, -64, -42, -53, 138]] ![![23, 0, 0, 0, 0], ![-6, -12, -4, -5, 13]]
  ![![23, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0, 0], ![-138, -276, -92, -115, 299]], ![![-2461, -1472, -966, -1219, 3174], ![1725, 690, 391, 598, -1541]]]
 hmul := by decide
 f :=  ![![![![15913976870892186, -398118601868892, 5817003256222630, 4271405153559423, -10657728546552484], ![-11907910778295484, 12084777128869974, 25176583989016, 0, 0]], ![![37364689, 18, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![23, 0, 0, 0, 0]], ![![-6, -12, -4, -5, 13]]], ![![![-107, -64, -42, -53, 138]], ![![75, 30, 17, 26, -67]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : PrimesBelowPCertificate 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI23N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
