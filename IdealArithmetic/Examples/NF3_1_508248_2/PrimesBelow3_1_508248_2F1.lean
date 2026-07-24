
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![-2, -16, 10], ![138, 4, -20]]]
  hmulB := by decide  
  f := ![![![137, 1088, -680], ![0, 2516, 0]], ![![69, 544, -340], ![1, 1258, 0]], ![![34, 235, -147], ![9, 544, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-8, 0, 37]], ![![-1, 1, 0], ![6, -16, 10], ![6, 4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![74427079, -3815821, -2085524]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![74427079, -3815821, -2085524]] 
 ![![37, 0, 0], ![22, 1, 0], ![21, 0, 1]] where
  M :=![![![74427079, -3815821, -2085524], ![-280170670, 58453341, -33987162], ![-409793954, -42375096, 71631101]]]
  hmulB := by decide  
  f := ![![![2746867920440889, 361705739159225, 251594772025686]], ![![2552101657052048, 336059047253109, 233755481948810]], ![![2527305705399819, 332793932846339, 231484338237575]]]
  g := ![![![5464085, -3815821, -2085524], ![-23038210, 58453341, -33987162], ![-26534999, -42375096, 71631101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-4, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-4, 1, 0]] 
 ![![37, 0, 0], ![33, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-4, 1, 0], ![-2, -2, 10], ![138, 4, -6]]]
  hmulB := by decide  
  f := ![![![-121, -127, 630], ![37, -2331, 0]], ![![-107, -113, 560], ![38, -2072, 0]], ![![-120, -123, 613], ![15, -2268, 0]]]
  g := ![![![1, 0, 0], ![-33, 37, 0], ![-36, 0, 37]], ![![-1, 1, 0], ![-8, -2, 10], ![6, 4, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-18, 1, 0]] ![![74427079, -3815821, -2085524]]
  ![![37, 0, 0], ![12, 8, 1]] where
 M := ![![![2753801923, -141185377, -77164388]], ![![-1619858092, 127138119, 3552270]]]
 hmul := by decide  
 g := ![![![![67883251, -8178373, -2630843], ![20176803, 0, 0]]], ![![![-39994600, 5959731, 411453], ![-11671491, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![12, 8, 1]] ![![37, 0, 0], ![-4, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-148, 37, 0]], ![![444, 296, 37], ![74, 0, 74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-4, 1, 0]]], ![![![12, 8, 1]], ![![2, 0, 2]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, -3, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, -3, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![16, 38, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, -3, 1], ![144, 14, -32], ![-470, 1, 27]]]
  hmulB := by decide  
  f := ![![![-15, 3, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -38, 41]], ![![0, -1, 1], ![16, 30, -32], ![-22, -25, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [8, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 40], [0, 1]]
 g := ![![[17, 36], [18], [18], [20, 5], [1]], ![[0, 5], [18], [18], [37, 36], [1]]]
 h' := ![![[28, 40], [4, 35], [36, 10], [4, 10], [33, 28], [0, 1]], ![[0, 1], [0, 6], [29, 31], [38, 31], [38, 13], [28, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [2, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [8, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1374, 383, 50]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, -37, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-9, 1, 0]] 
 ![![41, 0, 0], ![32, 1, 0], ![14, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-9, 1, 0], ![-2, -7, 10], ![138, 4, -11]]]
  hmulB := by decide  
  f := ![![![-260, -946, 1350], ![41, -5535, 0]], ![![-200, -736, 1050], ![42, -4305, 0]], ![![-89, -323, 461], ![13, -1890, 0]]]
  g := ![![![1, 0, 0], ![-32, 41, 0], ![-14, 0, 41]], ![![-1, 1, 0], ![2, -7, 10], ![4, 4, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![16, -3, 1]] ![![41, 0, 0], ![-9, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-369, 41, 0]], ![![656, -123, 41], ![0, 41, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-9, 1, 0]]], ![![![16, -3, 1]], ![![0, 1, -1]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3601349828991, -474223348044, -329859613004]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-3601349828991, -474223348044, -329859613004]] 
 ![![43, 0, 0], ![0, 1, 0], ![17, 0, 1]] where
  M :=![![![-3601349828991, -474223348044, -329859613004], ![-44572179898464, -5869234977095, -4082514254432], ![-46970683701848, -6185068361228, -4302201197923]]]
  hmulB := by decide  
  f := ![![![9388811, 703700, -1387628]], ![![-4486048, 121993, 228192]], ![![7777385, -75848, -524335]]]
  g := ![![![46657292839, -474223348044, -329859613004], ![577454940160, -5869234977095, -4082514254432], ![608528759601, -6185068361228, -4302201197923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9388811, -703700, 1387628]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-9388811, -703700, 1387628]] 
 ![![43, 0, 0], ![0, 43, 0], ![30, 26, 1]] where
  M :=![![![-9388811, -703700, 1387628], ![192900064, -5245699, -9812256], ![-174817768, 15224364, -1043271]]]
  hmulB := by decide  
  f := ![![![3601349828991, 474223348044, 329859613004]], ![![44572179898464, 5869234977095, 4082514254432]], ![![30555531533294, 4023532051326, 2798682795425]]]
  g := ![![![-1186457, -855396, 1387628], ![11331808, 5810999, -9812256], ![-3337666, 984870, -1043271]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[40, 24], [40, 25], [1], [19, 24], [1]], ![[32, 19], [3, 18], [1], [11, 19], [1]]]
 h' := ![![[14, 42], [14, 14], [12, 5], [26, 42], [24, 14], [0, 1]], ![[0, 1], [38, 29], [39, 38], [12, 1], [5, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [8, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [19, 29, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11035, 2548, 1302]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1165, -728, 1302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-3601349828991, -474223348044, -329859613004]] ![![-9388811, -703700, 1387628]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 7, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 7, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![35, 7, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 7, 1], ![124, 6, 68], ![910, 41, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -7, 47]], ![![-1, 0, 1], ![-48, -10, 68], ![35, 4, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [22, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 46], [0, 1]]
 g := ![![[3, 25], [35, 18], [3, 2], [40, 32], [1]], ![[45, 22], [22, 29], [12, 45], [43, 15], [1]]]
 h' := ![![[28, 46], [29, 5], [28, 21], [13, 7], [25, 28], [0, 1]], ![[0, 1], [28, 42], [5, 26], [21, 40], [10, 19], [28, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [23, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [22, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![944050, 104069, 45652]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13910, -4585, 45652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-21, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-21, 1, 0]] 
 ![![47, 0, 0], ![26, 1, 0], ![21, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-21, 1, 0], ![-2, -19, 10], ![138, 4, -23]]]
  hmulB := by decide  
  f := ![![![981, 10112, -5320], ![-188, 25004, 0]], ![![547, 5588, -2940], ![-93, 13818, 0]], ![![441, 4518, -2377], ![-78, 11172, 0]]]
  g := ![![![1, 0, 0], ![-26, 47, 0], ![-21, 0, 47]], ![![-1, 1, 0], ![6, -19, 10], ![11, 4, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-12, 7, 1]] ![![47, 0, 0], ![-21, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-987, 47, 0]], ![![-564, 329, 47], ![376, -141, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-21, 1, 0]]], ![![![-12, 7, 1]], ![![8, -3, 1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-24, 21, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-24, 21, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![29, 21, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-24, 21, 1], ![96, 22, 208], ![2842, 97, -61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -21, 53]], ![![-1, 0, 1], ![-112, -82, 208], ![87, 26, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [50, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 52], [0, 1]]
 g := ![![[45, 4], [43], [10, 29], [16], [29, 1]], ![[2, 49], [43], [3, 24], [16], [5, 52]]]
 h' := ![![[29, 52], [22, 2], [30, 19], [38, 33], [34, 49], [0, 1]], ![[0, 1], [27, 51], [51, 34], [41, 20], [24, 4], [29, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [27, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [50, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6983, 2632, 514]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-413, -154, 514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![8, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![-2, 6, 10], ![138, 4, 2]]]
  hmulB := by decide  
  f := ![![![637, -1921, -3200], ![53, 16960, 0]], ![![48, -144, -240], ![1, 1272, 0]], ![![96, -290, -483], ![10, 2560, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-8, 0, 53]], ![![0, 1, 0], ![-2, 6, 10], ![2, 4, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-24, 21, 1]] ![![53, 0, 0], ![4, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![212, 53, 0]], ![![-1272, 1113, 53], ![0, 106, 212]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![4, 1, 0]]], ![![![-24, 21, 1]], ![![0, 2, 4]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, -29, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, -29, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![26, 30, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, -29, 1], ![196, -28, -292], ![-4058, -103, 89]]]
  hmulB := by decide  
  f := ![![![-25, 29, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -30, 59]], ![![0, -1, 1], ![132, 148, -292], ![-108, -47, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [38, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 58], [0, 1]]
 g := ![![[11, 7], [48, 5], [20], [56, 51], [54, 1]], ![[35, 52], [23, 54], [20], [37, 8], [49, 58]]]
 h' := ![![[54, 58], [5, 40], [23, 8], [55, 16], [13, 46], [0, 1]], ![[0, 1], [41, 19], [42, 51], [34, 43], [19, 13], [54, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [53, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [38, 5, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1396, 399, 90]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -39, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-3, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-3, 1, 0]] 
 ![![59, 0, 0], ![56, 1, 0], ![29, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-3, 1, 0], ![-2, -1, 10], ![138, 4, -5]]]
  hmulB := by decide  
  f := ![![![2803, 1406, -14040], ![-118, 82836, 0]], ![![2662, 1333, -13320], ![-58, 78588, 0]], ![![1378, 691, -6901], ![-53, 40716, 0]]]
  g := ![![![1, 0, 0], ![-56, 59, 0], ![-29, 0, 59]], ![![-1, 1, 0], ![-4, -1, 10], ![1, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, -29, 1]] ![![59, 0, 0], ![-3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-177, 59, 0]], ![![1534, -1711, 59], ![118, 59, -295]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-3, 1, 0]]], ![![![26, -29, 1]], ![![2, 1, -5]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [11, 53, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 9, 18], [29, 51, 43], [0, 1]]
 g := ![![[59, 3, 1], [8, 48], [0, 54, 27], [57, 60, 39], [1]], ![[8, 55, 9, 24], [21, 42], [25, 34, 47, 7], [15, 53], [53, 41, 21, 37]], ![[3, 34, 31, 10], [14, 45], [36, 7, 47, 21], [25, 47, 11, 30], [25, 31, 44, 24]]]
 h' := ![![[22, 9, 18], [34, 24, 60], [0, 0, 29], [44, 39, 37], [50, 8, 51], [0, 1]], ![[29, 51, 43], [27, 55, 15], [21, 33, 15], [18, 25, 27], [0, 48], [22, 9, 18]], ![[0, 1], [51, 43, 47], [49, 28, 17], [7, 58, 58], [19, 5, 10], [29, 51, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 39], []]
 b := ![[], [4, 47, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [11, 53, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12544833, 1504260, 637938]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205653, 24660, 10458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![6, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![6, 1, 0]] 
 ![![67, 0, 0], ![6, 1, 0], ![62, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![6, 1, 0], ![-2, 8, 10], ![138, 4, 4]]]
  hmulB := by decide  
  f := ![![![2677, -10754, -13440], ![134, 90048, 0]], ![![234, -961, -1200], ![68, 8040, 0]], ![![2480, -9951, -12437], ![93, 83328, 0]]]
  g := ![![![1, 0, 0], ![-6, 67, 0], ![-62, 0, 67]], ![![0, 1, 0], ![-10, 8, 10], ![-2, 4, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![19, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![19, 1, 0]] 
 ![![67, 0, 0], ![19, 1, 0], ![47, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![19, 1, 0], ![-2, 21, 10], ![138, 4, 17]]]
  hmulB := by decide  
  f := ![![![2205, -23944, -11400], ![268, 76380, 0]], ![![608, -6785, -3230], ![135, 21641, 0]], ![![1538, -16797, -7997], ![219, 53580, 0]]]
  g := ![![![1, 0, 0], ![-19, 67, 0], ![-47, 0, 67]], ![![0, 1, 0], ![-13, 21, 10], ![-11, 4, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203191, -5951, -9932]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![203191, -5951, -9932]] 
 ![![67, 0, 0], ![42, 1, 0], ![16, 0, 1]] where
  M :=![![![203191, -5951, -9932], ![-1358714, 151561, -39646], ![-265046, -152920, 165433]]]
  hmulB := by decide  
  f := ![![![-19010524593, -2503293223, -1741237198]], ![![-15428748952, -2031647391, -1413170450]], ![![-8240501122, -1085103702, -754774915]]]
  g := ![![![9135, -5951, -9932], ![-105820, 151561, -39646], ![52398, -152920, 165433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![6, 1, 0]] ![![67, 0, 0], ![19, 1, 0]]
  ![![-19010524593, -2503293223, -1741237198]] where
 M := ![![![4489, 0, 0], ![1273, 67, 0]], ![![402, 67, 0], ![112, 27, 10]]]
 hmul := by decide  
 g := ![![![![13613797, -398717, -665444]], ![![2501915, 38492, -228354]]], ![![![-139568, 115855, -99238]], ![![-247438, 28305, -7888]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-19010524593, -2503293223, -1741237198]] ![![203191, -5951, -9932]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![3, -31, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![3, -31, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![3, 40, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![3, -31, 1], ![200, -55, -312], ![-4334, -111, 70]]]
  hmulB := by decide  
  f := ![![![-2, 31, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -40, 71]], ![![0, -1, 1], ![16, 175, -312], ![-64, -41, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [17, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 70], [0, 1]]
 g := ![![[31, 60], [64, 20], [52, 45], [36], [48], [1]], ![[6, 11], [32, 51], [51, 26], [36], [48], [1]]]
 h' := ![![[41, 70], [48, 42], [39, 34], [4, 51], [41, 6], [54, 41], [0, 1]], ![[0, 1], [66, 29], [13, 37], [36, 20], [3, 65], [31, 30], [41, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [37, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [17, 30, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3626, 454, 22]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -6, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![28, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![28, 1, 0]] 
 ![![71, 0, 0], ![28, 1, 0], ![1, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![28, 1, 0], ![-2, 30, 10], ![138, 4, 26]]]
  hmulB := by decide  
  f := ![![![1039, -16833, -5610], ![213, 39831, 0]], ![![414, -6631, -2210], ![72, 15691, 0]], ![![-11, -238, -79], ![68, 561, 0]]]
  g := ![![![1, 0, 0], ![-28, 71, 0], ![-1, 0, 71]], ![![0, 1, 0], ![-12, 30, 10], ![0, 4, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![3, -31, 1]] ![![71, 0, 0], ![28, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1988, 71, 0]], ![![213, -2201, 71], ![284, -923, -284]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![28, 1, 0]]], ![![![3, -31, 1]], ![![4, -13, -4]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165, 7, 6]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-165, 7, 6]] 
 ![![73, 0, 0], ![0, 73, 0], ![9, 62, 1]] where
  M :=![![![-165, 7, 6], ![814, -127, 58], ![630, 106, -149]]]
  hmulB := by decide  
  f := ![![![-175, -23, -16]], ![![-2162, -285, -198]], ![![-1889, -249, -173]]]
  g := ![![![-3, -5, 6], ![4, -51, 58], ![27, 128, -149]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [26, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 72], [0, 1]]
 g := ![![[65, 12], [23], [46], [54, 38], [48], [1]], ![[6, 61], [23], [46], [1, 35], [48], [1]]]
 h' := ![![[62, 72], [71, 42], [42, 60], [56, 22], [12, 44], [47, 62], [0, 1]], ![[0, 1], [47, 31], [39, 13], [33, 51], [39, 29], [22, 11], [62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [38, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [26, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2670, 1579, 540]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -437, 540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 23, 16]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![175, 23, 16]] 
 ![![73, 0, 0], ![39, 1, 0], ![37, 0, 1]] where
  M :=![![![175, 23, 16], ![2162, 285, 198], ![2278, 300, 209]]]
  hmulB := by decide  
  f := ![![![165, -7, -6]], ![![77, -2, -4]], ![![75, -5, -1]]]
  g := ![![![-18, 23, 16], ![-223, 285, 198], ![-235, 300, 209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-165, 7, 6]] ![![175, 23, 16]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [12, 53, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 39, 36], [56, 39, 43], [0, 1]]
 g := ![![[15, 41, 19], [17, 56, 76], [14, 16, 42], [1, 51, 9], [34, 1], []], ![[18, 63, 38, 16], [27, 50, 38, 52], [68, 48, 13, 46], [9, 36, 21, 72], [76, 20], [25, 32]], ![[5, 57, 1, 68], [40, 6, 57, 27], [27, 50, 10, 29], [78, 6, 7, 30], [20, 20], [18, 32]]]
 h' := ![![[57, 39, 36], [33, 28, 16], [69, 0, 47], [67, 57, 68], [66, 3, 76], [0, 0, 1], [0, 1]], ![[56, 39, 43], [70, 12, 52], [27, 27, 16], [28, 3, 43], [1, 43, 70], [26, 51, 39], [57, 39, 36]], ![[0, 1], [52, 39, 11], [7, 52, 16], [53, 19, 47], [6, 33, 12], [76, 28, 39], [56, 39, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 29], []]
 b := ![[], [2, 31, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [12, 53, 45, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258488, -42265, -42265]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3272, -535, -535]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB202I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB202I1 : PrimesBelowBoundCertificateInterval O 31 79 202 where
  m := 11
  g := ![3, 2, 2, 2, 2, 2, 1, 3, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB202I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![43, 1849]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I47N1, I53N1, I59N1, I67N0, I67N1, I67N2, I71N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N2], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
