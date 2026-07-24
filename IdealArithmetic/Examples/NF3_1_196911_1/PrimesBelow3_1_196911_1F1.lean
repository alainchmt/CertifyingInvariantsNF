
import IdealArithmetic.Examples.NF3_1_196911_1.RI3_1_196911_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 20, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 31, 28], [20, 5, 9], [0, 1]]
 g := ![![[27, 2, 25], [11, 21], [36, 34, 34], [31, 1], []], ![[13, 19, 34, 12], [27, 28], [5, 11, 33, 26], [16, 25], [29, 7]], ![[14, 34, 23, 30], [36, 25], [11, 15, 3, 9], [35, 36], [11, 7]]]
 h' := ![![[11, 31, 28], [25, 7, 32], [27, 1, 13], [14, 19, 16], [0, 0, 1], [0, 1]], ![[20, 5, 9], [8, 23, 23], [16, 10, 19], [28, 11, 20], [4, 24, 5], [11, 31, 28]], ![[0, 1], [20, 7, 19], [17, 26, 5], [7, 7, 1], [29, 13, 31], [20, 5, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 20], []]
 b := ![[], [4, 23, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 20, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184038, -2590, -6475]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4974, -70, -175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145901, -616967, 466982]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![145901, -616967, 466982]] 
 ![![41, 0, 0], ![0, 41, 0], ![33, 5, 1]] where
  M :=![![![145901, -616967, 466982], ![38459536, -471066, -3551817], ![-68319583, 7938694, 762868]]]
  hmulB := by decide  
  f := ![![![678961637310, 101899794704, 58813005411]], ![![5202905049343, 780861432014, 450685968109]], ![![1343465844971, 201629792129, 116373679554]]]
  g := ![![![-372305, -71997, 466982], ![3796817, 421659, -3551817], ![-2280347, 100594, 762868]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[13, 21], [33], [9], [35, 20], [1]], ![[0, 20], [33], [9], [7, 21], [1]]]
 h' := ![![[15, 40], [25, 12], [3, 22], [12, 38], [39, 15], [0, 1]], ![[0, 1], [0, 29], [5, 19], [8, 3], [18, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [32, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5589, 2873, 468]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-513, 13, 468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-678961637310, -101899794704, -58813005411]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-678961637310, -101899794704, -58813005411]] 
 ![![41, 0, 0], ![17, 1, 0], ![13, 0, 1]] where
  M :=![![![-678961637310, -101899794704, -58813005411], ![-5202905049343, -780861432014, -450685968109], ![-6661840365866, -999821091987, -577061842606]]]
  hmulB := by decide  
  f := ![![![-145901, 616967, -466982]], ![![-998533, 267305, -106997]], ![![1620070, 1997, -166674]]]
  g := ![![![44339120561, -101899794704, -58813005411], ![339772119032, -780861432014, -450685968109], ![435046881751, -999821091987, -577061842606]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![145901, -616967, 466982]] ![![-678961637310, -101899794704, -58813005411]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49080, 41269, -27229]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-49080, 41269, -27229]] 
 ![![43, 0, 0], ![0, 43, 0], ![6, 14, 1]] where
  M :=![![![-49080, 41269, -27229], ![-2231927, -7811, 233574], ![4433651, -462893, -90349]]]
  hmulB := by decide  
  f := ![![![-2530825247, -379830846, -219225109]], ![![-19393795957, -2910656093, -1679929121]], ![![-7244885188, -1087325517, -627566343]]]
  g := ![![![2658, 9825, -27229], ![-84497, -76229, 233574], ![115715, 18651, -90349]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [23, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 42], [0, 1]]
 g := ![![[32, 15], [40, 6], [15], [19, 25], [1]], ![[0, 28], [10, 37], [15], [23, 18], [1]]]
 h' := ![![[38, 42], [26, 31], [5, 7], [36, 31], [20, 38], [0, 1]], ![[0, 1], [0, 12], [13, 36], [10, 12], [2, 5], [38, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [2, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [23, 5, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![857855, 312937, 20347]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17111, 653, 20347]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2530825247, 379830846, 219225109]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![2530825247, 379830846, 219225109]] 
 ![![43, 0, 0], ![17, 1, 0], ![8, 0, 1]] where
  M :=![![![2530825247, 379830846, 219225109], ![19393795957, 2910656093, 1679929121], ![24831968204, 3726826853, 2150994401]]]
  hmulB := by decide  
  f := ![![![49080, -41269, 27229]], ![![71309, -16134, 5333]], ![![-93977, 3087, 7167]]]
  g := ![![![-132095349, 379830846, 219225109], ![-1012250944, 2910656093, 1679929121], ![-1296094035, 3726826853, 2150994401]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-49080, 41269, -27229]] ![![2530825247, 379830846, 219225109]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, 16, 9]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![105, 16, 9]] 
 ![![47, 0, 0], ![0, 47, 0], ![43, 7, 1]] where
  M :=![![![105, 16, 9], ![797, 121, 71], ![1054, 153, 89]]]
  hmulB := by decide  
  f := ![![![-2, -1, 1]], ![![83, -3, -6]], ![![8, -1, 0]]]
  g := ![![![-6, -1, 9], ![-48, -8, 71], ![-59, -10, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [33, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 46], [0, 1]]
 g := ![![[15, 2], [14, 37], [31, 2], [31, 14], [1]], ![[12, 45], [29, 10], [28, 45], [10, 33], [1]]]
 h' := ![![[22, 46], [8, 7], [11, 32], [11, 40], [14, 22], [0, 1]], ![[0, 1], [21, 40], [10, 15], [45, 7], [28, 25], [22, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [33, 25, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3601, 2859, -216]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![121, 93, -216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -1, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2, -1, 1]] 
 ![![47, 0, 0], ![13, 1, 0], ![11, 0, 1]] where
  M :=![![![-2, -1, 1], ![83, -3, -6], ![-119, 17, -1]]]
  hmulB := by decide  
  f := ![![![105, 16, 9]], ![![46, 7, 4]], ![![47, 7, 4]]]
  g := ![![![0, -1, 1], ![4, -3, -6], ![-7, 17, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![105, 16, 9]] ![![-2, -1, 1]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [3, 50, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 21, 40], [37, 31, 13], [0, 1]]
 g := ![![[32, 7, 29], [11, 46], [22, 52, 7], [13, 36], [1]], ![[0, 35, 13, 9], [4, 13], [4, 35, 41, 17], [42, 10], [44, 9, 32, 29]], ![[3, 36, 50, 43], [11, 28], [17, 21, 32, 6], [38, 43], [23, 25, 44, 24]]]
 h' := ![![[10, 21, 40], [30, 35, 20], [40, 15, 29], [23, 19, 22], [50, 3, 47], [0, 1]], ![[37, 31, 13], [50, 0, 6], [3, 31, 15], [9, 41, 11], [20, 45, 40], [10, 21, 40]], ![[0, 1], [4, 18, 27], [39, 7, 9], [52, 46, 20], [22, 5, 19], [37, 31, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 31], []]
 b := ![[], [35, 13, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [3, 50, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-184122, -2650, -6625]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3474, -50, -125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-737052227, 28373237, 52959379]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-737052227, 28373237, 52959379]] 
 ![![59, 0, 0], ![0, 59, 0], ![4, 41, 1]] where
  M :=![![![-737052227, 28373237, 52959379], ![4558293689, -708678990, 88906806], ![611106259, 900309443, -765425464]]]
  hmulB := by decide  
  f := ![![![-7837242504390378, -1176227578051235, -678877510140648]], ![![-60057043518057550, -9013470082441613, -5202260380115527]], ![![-43569241746567695, -6538950870588171, -3774054246637938]]]
  g := ![![![-16082877, -36321378, 52959379], ![71231635, -73794204, 88906806], ![62250985, 547165313, -765425464]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [56, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 58], [0, 1]]
 g := ![![[37, 41], [30, 20], [51], [10, 49], [52, 1]], ![[45, 18], [8, 39], [51], [21, 10], [45, 58]]]
 h' := ![![[52, 58], [31, 49], [50, 43], [30, 46], [38, 52], [0, 1]], ![[0, 1], [42, 10], [44, 16], [3, 13], [28, 7], [52, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [26, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [56, 7, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24292, 1547, 2002]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![276, -1365, 2002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92056377, -21618505, 7501873]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![92056377, -21618505, 7501873]] 
 ![![59, 0, 0], ![32, 1, 0], ![37, 0, 1]] where
  M :=![![![92056377, -21618505, 7501873], ![594422195, 70437872, -115594398], ![-2092636607, 127531841, 113674882]]]
  hmulB := by decide  
  f := ![![![-22748983174157822, -3414208679529603, -1970562101000734]], ![![-15293112839274100, -2295218128790419, -1324719805570691]], ![![-18049508538471707, -2708902997620471, -1563484275112803]]]
  g := ![![![8581004, -21618505, 7501873], ![44362763, 70437872, -115594398], ![-175925867, 127531841, 113674882]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-737052227, 28373237, 52959379]] ![![92056377, -21618505, 7501873]]
  ![![59, 0, 0]] where
 M := ![![![-161809411039993417, 24686524792779038, -2788908293029219]]]
 hmul := by decide  
 g := ![![![![-2742532390508363, 418415674453882, -47269632085241]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, 5, 7]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-107, 5, 7]] 
 ![![61, 0, 0], ![0, 1, 0], ![37, 0, 1]] where
  M :=![![![-107, 5, 7], ![605, -102, 18], ![187, 119, -112]]]
  hmulB := by decide  
  f := ![![![-9282, -1393, -804]], ![![-1166, -175, -101]], ![![-7123, -1069, -617]]]
  g := ![![![-6, 5, 7], ![-1, -102, 18], ![71, 119, -112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27545, -4134, -2386]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-27545, -4134, -2386]] 
 ![![61, 0, 0], ![8, 1, 0], ![47, 0, 1]] where
  M :=![![![-27545, -4134, -2386], ![-211078, -31679, -18284], ![-270266, -40562, -23411]]]
  hmulB := by decide  
  f := ![![![-1461, 142, 38]], ![![-134, -3, 16]], ![![-949, 120, 3]]]
  g := ![![![1929, -4134, -2386], ![14782, -31679, -18284], ![18927, -40562, -23411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-8, 1, 0]] 
 ![![61, 0, 0], ![53, 1, 0], ![38, 0, 1]] where
  M :=![![![-8, 1, 0], ![2, -7, 5], ![85, 0, -9]]]
  hmulB := by decide  
  f := ![![![-63, -9, -5]], ![![-62, -9, -5]], ![![-49, -7, -4]]]
  g := ![![![-1, 1, 0], ![3, -7, 5], ![7, 0, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-107, 5, 7]] ![![-27545, -4134, -2386]]
  ![![63, 9, 5]] where
 M := ![![![63, 9, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![63, 9, 5]] ![![-8, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1276004, -191505, -110530]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-1276004, -191505, -110530]] 
 ![![67, 0, 0], ![0, 67, 0], ![24, 56, 1]] where
  M :=![![![-1276004, -191505, -110530], ![-9778060, -1467509, -846995], ![-12519905, -1879010, -1084499]]]
  hmulB := by decide  
  f := ![![![477, 85, -115]], ![![-9605, 562, 540]], ![![-7691, 471, 416]]]
  g := ![![![20548, 89525, -110530], ![157460, 686033, -846995], ![201613, 878402, -1084499]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 66], [0, 1]]
 g := ![![[33, 36], [3, 21], [29], [21], [59], [1]], ![[0, 31], [34, 46], [29], [21], [59], [1]]]
 h' := ![![[27, 66], [39, 6], [56, 50], [9, 30], [65, 17], [13, 27], [0, 1]], ![[0, 1], [0, 61], [66, 17], [15, 37], [55, 50], [5, 40], [27, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [60, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [54, 40, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2911, 868, -219]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 196, -219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![477, 85, -115]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![477, 85, -115]] 
 ![![67, 0, 0], ![56, 1, 0], ![32, 0, 1]] where
  M :=![![![477, 85, -115], ![-9605, 562, 540], ![11135, -1955, 392]]]
  hmulB := by decide  
  f := ![![![-1276004, -191505, -110530]], ![![-1212452, -181967, -105025]], ![![-796299, -119510, -68977]]]
  g := ![![![-9, 85, -115], ![-871, 562, 540], ![1613, -1955, 392]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-1276004, -191505, -110530]] ![![477, 85, -115]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 7, 4]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![47, 7, 4]] 
 ![![71, 0, 0], ![41, 1, 0], ![11, 0, 1]] where
  M :=![![![47, 7, 4], ![354, 54, 31], ![459, 68, 40]]]
  hmulB := by decide  
  f := ![![![52, -8, 1]], ![![31, -4, 0]], ![![-2, -1, 1]]]
  g := ![![![-4, 7, 4], ![-31, 54, 31], ![-39, 68, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-925, 154, -26]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-925, 154, -26]] 
 ![![71, 0, 0], ![46, 1, 0], ![65, 0, 1]] where
  M :=![![![-925, 154, -26], ![-1902, -771, 796], ![13974, -442, -1079]]]
  hmulB := by decide  
  f := ![![![1183741, 177658, 102538]], ![![894692, 134277, 77500]], ![![1247293, 187196, 108043]]]
  g := ![![![-89, 154, -26], ![-256, -771, 796], ![1471, -442, -1079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8462, -1270, -733]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-8462, -1270, -733]] 
 ![![71, 0, 0], ![55, 1, 0], ![66, 0, 1]] where
  M :=![![![-8462, -1270, -733], ![-64845, -9732, -5617], ![-83028, -12461, -7192]]]
  hmulB := by decide  
  f := ![![![893, -73, -34]], ![![649, -45, -31]], ![![759, -76, -18]]]
  g := ![![![1546, -1270, -733], ![11847, -9732, -5617], ![15169, -12461, -7192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![47, 7, 4]] ![![-925, 154, -26]]
  ![![-893, 73, 34]] where
 M := ![![![-893, 73, 34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-893, 73, 34]] ![![-8462, -1270, -733]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![853, 128, 74]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![853, 128, 74]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 55, 1]] where
  M :=![![![853, 128, 74], ![6546, 981, 566], ![8364, 1258, 725]]]
  hmulB := by decide  
  f := ![![![-11, 4, -2]], ![![-162, -7, 22]], ![![-124, -3, 15]]]
  g := ![![![-39, -54, 74], ![-298, -413, 566], ![-382, -529, 725]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [57, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 72], [0, 1]]
 g := ![![[7, 41], [50], [35], [21, 18], [61], [1]], ![[0, 32], [50], [35], [66, 55], [61], [1]]]
 h' := ![![[39, 72], [47, 25], [14, 59], [44, 20], [64, 50], [16, 39], [0, 1]], ![[0, 1], [0, 48], [52, 14], [21, 53], [43, 23], [4, 34], [39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [19, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [57, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1927, 1835, 405]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -280, 405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 4, -2]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-11, 4, -2]] 
 ![![73, 0, 0], ![18, 1, 0], ![5, 0, 1]] where
  M :=![![![-11, 4, -2], ![-162, -7, 22], ![408, -34, -15]]]
  hmulB := by decide  
  f := ![![![853, 128, 74]], ![![300, 45, 26]], ![![173, 26, 15]]]
  g := ![![![-1, 4, -2], ![-2, -7, 22], ![15, -34, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![853, 128, 74]] ![![-11, 4, -2]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 13, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 71, 29], [5, 7, 50], [0, 1]]
 g := ![![[33, 22, 13], [63, 21, 21], [55, 9, 67], [12, 64, 72], [64, 1], []], ![[34, 53, 77, 43], [7, 39, 70, 66], [0, 41, 51, 14], [45, 2, 2, 70], [52, 49], [35, 51]], ![[14, 58, 7, 62], [75, 17, 42, 49], [58, 0, 1, 23], [42, 62, 70, 10], [41, 64], [14, 51]]]
 h' := ![![[59, 71, 29], [48, 36, 48], [72, 1, 10], [43, 18, 15], [45, 34, 54], [0, 0, 1], [0, 1]], ![[5, 7, 50], [58, 29, 37], [0, 35, 20], [0, 39, 74], [48, 55, 21], [58, 28, 7], [59, 71, 29]], ![[0, 1], [44, 14, 73], [65, 43, 49], [36, 22, 69], [8, 69, 4], [62, 51, 71], [5, 7, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 25], []]
 b := ![[], [42, 67, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [3, 13, 15, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1485437, -38315, -76630]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18803, -485, -970]
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



lemma PB126I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB126I1 : PrimesBelowBoundCertificateInterval O 31 79 126 where
  m := 11
  g := ![1, 2, 2, 2, 1, 2, 3, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB126I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N1, I47N1, I59N1, I61N0, I61N1, I61N2, I67N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[], [I41N1], [I43N1], [I47N1], [], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
