
import IdealArithmetic.Examples.NF3_1_230520_1.RI3_1_230520_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [20, 7, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 32, 25], [16, 4, 12], [0, 1]]
 g := ![![[36, 21, 3], [7, 7], [1, 9, 36], [36, 1], []], ![[4, 35, 8, 12], [27, 4], [11, 8, 2, 36], [35, 16], [13, 33]], ![[18, 19, 1, 1], [7, 10], [36, 30, 5, 36], [11, 25], [26, 33]]]
 h' := ![![[20, 32, 25], [1, 23, 15], [17, 28, 28], [20, 24, 31], [0, 0, 1], [0, 1]], ![[16, 4, 12], [8, 13, 6], [20, 20, 35], [30, 36, 21], [29, 11, 4], [20, 32, 25]], ![[0, 1], [35, 1, 16], [29, 26, 11], [27, 14, 22], [32, 26, 32], [16, 4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 24], []]
 b := ![[], [30, 15, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [20, 7, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-188071, 53613, -3996]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5083, 1449, -108]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 19, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 12, 23], [39, 28, 18], [0, 1]]
 g := ![![[40, 20, 18], [27, 2], [4, 9], [4, 33, 1], []], ![[28, 8, 22, 20], [26, 25], [18, 31], [3, 11, 24, 33], [10, 37]], ![[24, 16, 12, 39], [2, 21], [9, 37], [31, 25, 28, 9], [15, 37]]]
 h' := ![![[35, 12, 23], [18, 0, 31], [26, 12, 24], [24, 40, 3], [0, 0, 1], [0, 1]], ![[39, 28, 18], [1, 13, 7], [3, 39, 5], [31, 21, 20], [14, 11, 28], [35, 12, 23]], ![[0, 1], [21, 28, 3], [3, 31, 12], [21, 21, 18], [12, 30, 12], [39, 28, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 14], []]
 b := ![[], [24, 7, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 19, 8, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3912097, -716762, 224434]
  a := ![2, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![95417, -17482, 5474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![198, -37, 20]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![198, -37, 20]] 
 ![![43, 0, 0], ![0, 43, 0], ![40, 39, 1]] where
  M :=![![![198, -37, 20], ![-2017, 378, -202], ![3363, -633, 341]]]
  hmulB := by decide  
  f := ![![![24, -1, -2]], ![![197, 6, -8]], ![![204, 5, -9]]]
  g := ![![![-14, -19, 20], ![141, 192, -202], ![-239, -324, 341]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[5, 21], [40, 17], [31], [8, 14], [1]], ![[0, 22], [38, 26], [31], [19, 29], [1]]]
 h' := ![![[10, 42], [37, 35], [17, 24], [16, 26], [2, 10], [0, 1]], ![[0, 1], [0, 8], [42, 19], [18, 17], [16, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [20, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [41, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1527470, -1600105, 987460]
  a := ![-65, 1, -326]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-954090, -932815, 987460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, -1, -2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![24, -1, -2]] 
 ![![43, 0, 0], ![23, 1, 0], ![41, 0, 1]] where
  M :=![![![24, -1, -2], ![197, 6, -8], ![129, 21, 5]]]
  hmulB := by decide  
  f := ![![![198, -37, 20]], ![![59, -11, 6]], ![![267, -50, 27]]]
  g := ![![![3, -1, -2], ![9, 6, -8], ![-13, 21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![198, -37, 20]] ![![24, -1, -2]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153865735145667405630561886883, 86712718092583511783117284092, 60694478041758243832818770296]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-153865735145667405630561886883, 86712718092583511783117284092, 60694478041758243832818770296]] 
 ![![47, 0, 0], ![0, 47, 0], ![40, 24, 1]] where
  M :=![![![-153865735145667405630561886883, 86712718092583511783117284092, 60694478041758243832818770296], ![-5922040608041482627665940975212, 392384567230156788864807045781, 580970786597259314531522474848], ![-9494976261792141324020892679548, -130002707793122051444225997612, 479097285322740300647924329873]]]
  hmulB := by decide  
  f := ![![![5606769284443620694301278103918920084410465125311813510187, -1051793070949608244934136859701392161872830533766224166244, 565148500820405948669826643193904182423673802365428629720]], ![![-57001494652169797163246974535897906221816536967943658508524, 10693105791827274232329717892664057726223529346600671177667, -5745609924877243520934994515014448788813309400231916367744]], ![![-22300315186438833555903066281750291162938790774697882995420, 4183392574787610390299853694694906526834912789965738184516, -2247816711560849799324494076587828469579186695704561715439]]]
  g := ![![![-54928613974808450190283248909, -29147973508715198727756025596, 60694478041758243832818770296], ![-620444086636847983168656169556, -288317325768171633189185794693, 580970786597259314531522474848], ![-609763142014930922339103529244, -247411437351891260999881062012, 479097285322740300647924329873]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [39, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[18, 9], [9, 1], [18, 37], [28, 9], [1]], ![[45, 38], [12, 46], [35, 10], [8, 38], [1]]]
 h' := ![![[3, 46], [25, 44], [3, 1], [36, 32], [8, 3], [0, 1]], ![[0, 1], [16, 3], [6, 46], [38, 15], [17, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [23, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [39, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5, -2729, 981]
  a := ![-2, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-835, -559, 981]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5606769284443620694301278103918920084410465125311813510187, 1051793070949608244934136859701392161872830533766224166244, -565148500820405948669826643193904182423673802365428629720]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-5606769284443620694301278103918920084410465125311813510187, 1051793070949608244934136859701392161872830533766224166244, -565148500820405948669826643193904182423673802365428629720]] 
 ![![47, 0, 0], ![43, 1, 0], ![21, 0, 1]] where
  M :=![![![-5606769284443620694301278103918920084410465125311813510187, 1051793070949608244934136859701392161872830533766224166244, -565148500820405948669826643193904182423673802365428629720], ![57001494652169797163246974535897906221816536967943658508524, -10693105791827274232329717892664057726223529346600671177667, 5745609924877243520934994515014448788813309400231916367744], ![-95650286511705127018432149462529261289055115807374763012356, 17943365150852563434454631385221092193210581839377446941996, -9641312720877665987395581032962665564350698812834447011423]]]
  hmulB := by decide  
  f := ![![![153865735145667405630561886883, -86712718092583511783117284092, -60694478041758243832818770296]], ![![266771642963940022761278768323, -87681520110877612671039367271, -67890071114741782964738927608]], ![![270769291486194826431121112853, -35977965364917695659600786560, -37312368599992838747598266087]]]
  g := ![![![-829058570596771283072400075829931813064787834629477690097, 1051793070949608244934136859701392161872830533766224166244, -565148500820405948669826643193904182423673802365428629720], ![8428664580389797344974254449045722635837208541848984583523, -10693105791827274232329717892664057726223529346600671177667, 5745609924877243520934994515014448788813309400231916367744], ![-14143562145956050403503704198613196781824371485767693495283, 17943365150852563434454631385221092193210581839377446941996, -9641312720877665987395581032962665564350698812834447011423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-153865735145667405630561886883, 86712718092583511783117284092, 60694478041758243832818770296]] ![![-5606769284443620694301278103918920084410465125311813510187, 1051793070949608244934136859701392161872830533766224166244, -565148500820405948669826643193904182423673802365428629720]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191334, -35893, 19286]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![191334, -35893, 19286]] 
 ![![53, 0, 0], ![0, 53, 0], ![17, 2, 1]] where
  M :=![![![191334, -35893, 19286], ![-1945207, 364908, -196072], ![3264117, -612327, 329015]]]
  hmulB := by decide  
  f := ![![![492, -59, -64]], ![![6277, -84, -418]], ![![523, -14, -39]]]
  g := ![![![-2576, -1405, 19286], ![26189, 14284, -196072], ![-43946, -23969, 329015]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [27, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52], [0, 1]]
 g := ![![[19, 7], [42], [4, 11], [9], [17, 1]], ![[32, 46], [42], [32, 42], [9], [34, 52]]]
 h' := ![![[17, 52], [36, 31], [51, 25], [28, 45], [18, 50], [0, 1]], ![[0, 1], [33, 22], [52, 28], [51, 8], [20, 3], [17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [8, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [27, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1735, -466, 138]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -14, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-492, 59, 64]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-492, 59, 64]] 
 ![![53, 0, 0], ![40, 1, 0], ![25, 0, 1]] where
  M :=![![![-492, 59, 64], ![-6277, 84, 418], ![-6801, -429, 143]]]
  hmulB := by decide  
  f := ![![![-191334, 35893, -19286]], ![![-107701, 20204, -10856]], ![![-151839, 28484, -15305]]]
  g := ![![![-84, 59, 64], ![-379, 84, 418], ![128, -429, 143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![191334, -35893, 19286]] ![![-492, 59, 64]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-322903724608950416288877502, 60574616663795362536881421, -32547898194848323932141876]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-322903724608950416288877502, 60574616663795362536881421, -32547898194848323932141876]] 
 ![![59, 0, 0], ![0, 59, 0], ![2, 23, 1]] where
  M :=![![![-322903724608950416288877502, 60574616663795362536881421, -32547898194848323932141876], ![3282816537953779431818927145, -615834808362585331678154386, 330899801787923851289146650], ![-5508668576793016032169132539, 1033390022896883121814060929, -555260191698789969141272965]]]
  hmulB := by decide  
  f := ![![![-24408649520960, -2267197656279, 79665326754]], ![![-10154065004925, -23691661580174, -13523520610920]], ![![-1001749255676, -9678684245159, -5709161061595]]]
  g := ![![![-4369625902021250312281250, 13714852121106895135188891, -32547898194848323932141876], ![44424015836914097105773455, -139432716092963286632686904, 330899801787923851289146650], ![-74544884633820950743840451, 233972447999475464611243036, -555260191698789969141272965]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [5, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 58], [0, 1]]
 g := ![![[16, 12], [57, 28], [16], [34, 57], [38, 1]], ![[0, 47], [0, 31], [16], [17, 2], [17, 58]]]
 h' := ![![[38, 58], [10, 37], [28, 21], [7, 55], [46, 23], [0, 1]], ![[0, 1], [0, 22], [0, 38], [32, 4], [35, 36], [38, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [49, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [5, 21, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42785, 2422, 3948]
  a := ![2, 19, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-859, -1498, 3948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24408649520960, -2267197656279, 79665326754]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-24408649520960, -2267197656279, 79665326754]] 
 ![![59, 0, 0], ![38, 1, 0], ![25, 0, 1]] where
  M :=![![![-24408649520960, -2267197656279, 79665326754], ![-10154065004925, -23691661580174, -13523520610920], ![223257588070311, -21599758807821, -25958859236453]]]
  hmulB := by decide  
  f := ![![![-322903724608950416288877502, 60574616663795362536881421, -32547898194848323932141876]], ![![-152330932155700616731498609, 28576281777315905842768468, -15354581857903600985292282]], ![![-230190876135877566769340171, 43182295584606223478577906, -23202671975762679109234235]]]
  g := ![![![1012766580488, -2267197656279, 79665326754], ![20817238818893, -23691661580174, -13523520610920], ![28695252604726, -21599758807821, -25958859236453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-322903724608950416288877502, 60574616663795362536881421, -32547898194848323932141876]] ![![-24408649520960, -2267197656279, 79665326754]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [58, 15, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 33, 12], [51, 27, 49], [0, 1]]
 g := ![![[38, 19, 60], [6, 49], [60, 54, 1], [50, 15, 19], [1]], ![[19, 46, 33, 15], [14, 20], [44, 58, 54, 27], [39, 49, 0, 56], [40, 40, 49, 20]], ![[50, 28, 46, 13], [57, 12], [56, 12, 16, 47], [50, 50, 31, 46], [12, 49, 7, 41]]]
 h' := ![![[53, 33, 12], [27, 25, 11], [58, 46, 7], [28, 36, 1], [3, 46, 43], [0, 1]], ![[51, 27, 49], [57, 4, 48], [36, 14, 9], [16, 32, 32], [35, 0, 5], [53, 33, 12]], ![[0, 1], [36, 32, 2], [29, 1, 45], [52, 54, 28], [12, 15, 13], [51, 27, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 19], []]
 b := ![[], [44, 55, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [58, 15, 18, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2715964, 430416, -158844]
  a := ![-2, 3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44524, 7056, -2604]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19489248118655, 1982681094984, 39143302552]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![19489248118655, 1982681094984, 39143302552]] 
 ![![67, 0, 0], ![0, 67, 0], ![45, 57, 1]] where
  M :=![![![19489248118655, 1982681094984, 39143302552], ![-1892505857664, 19841537841623, 11935229872456], ![-196872577941696, 17256980316576, 21824218936607]]]
  hmulB := by decide  
  f := ![![![-3388955804653283344184515, 635745837264729428850408, -341598377814555262591624]], ![![34453985240905700425421184, -6463341204984280707509131, 3472876645773821310510824]], ![![26172526646272198346916243, -4909793997083437048227225, 2638126066264675770206495]]]
  g := ![![![264594022445, -3708763440, 39143302552], ![-8044445524152, -9857709923707, 11935229872456], ![-17596454180433, -18309305956269, 21824218936607]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [58, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 66], [0, 1]]
 g := ![![[32, 60], [8, 36], [9], [24], [65], [1]], ![[26, 7], [58, 31], [9], [24], [65], [1]]]
 h' := ![![[20, 66], [5, 44], [37, 61], [31, 64], [63, 52], [9, 20], [0, 1]], ![[0, 1], [14, 23], [51, 6], [38, 3], [31, 15], [7, 47], [20, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [40, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [58, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4379, -1893, 1938]
  a := ![2, 1, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1367, -1677, 1938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3388955804653283344184515, 635745837264729428850408, -341598377814555262591624]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-3388955804653283344184515, 635745837264729428850408, -341598377814555262591624]] 
 ![![67, 0, 0], ![59, 1, 0], ![23, 0, 1]] where
  M :=![![![-3388955804653283344184515, 635745837264729428850408, -341598377814555262591624], ![34453985240905700425421184, -6463341204984280707509131, 3472876645773821310510824], ![-57814862221989884517316032, 10845688202600893798528032, -5827595367719551278658723]]]
  hmulB := by decide  
  f := ![![![19489248118655, 1982681094984, 39143302552]], ![![17133927360343, 2042085409637, 212607234672]], ![![3751942220707, 938188738824, 339171864109]]]
  g := ![![![-493152201694590277712705, 635745837264729428850408, -341598377814555262591624], ![5013656022122095104876283, -6463341204984280707509131, 3472876645773821310510824], ![-8413071234595417003303273, 10845688202600893798528032, -5827595367719551278658723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![19489248118655, 1982681094984, 39143302552]] ![![-3388955804653283344184515, 635745837264729428850408, -341598377814555262591624]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-429130778449340838906304538922003248927443879, 80502113856646390616548500656797909764015978, -43255322948535613061822742164465377181496120]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-429130778449340838906304538922003248927443879, 80502113856646390616548500656797909764015978, -43255322948535613061822742164465377181496120]] 
 ![![71, 0, 0], ![0, 71, 0], ![68, 20, 1]] where
  M :=![![![-429130778449340838906304538922003248927443879, 80502113856646390616548500656797909764015978, -43255322948535613061822742164465377181496120], ![4362779085761672083736999974938870250732131858, -818428684986161356462709218402191643560908959, 439757360191342730637468261776322081402599748], ![-7320879427579958475110960432556012408915140022, 1373348868937851711476277638378161845598585602, -737926571129514965846160717745393733796892981]]]
  hmulB := by decide  
  f := ![![![34061610560381579077627, 1942736174686549448082, -838855053370246183584]], ![![84989386458340921622898, 26511915080049363425371, 10817561994749050504908]], ![![54031397067314804325778, 9752279054259229137514, 2644559824232960316731]]]
  g := ![![![35383537775367335905600590538896371822736511, 13318430603202234533140892168255006385830118, -43255322948535613061822742164465377181496120], ![-359728470524642726755082279237338468797811986, -135402477307225577031155978224346947487505689, 439757360191342730637468261776322081402599748], ![603635597313057171865182653156771288581318066, 227209581570819028569006929482901922838541482, -737926571129514965846160717745393733796892981]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [26, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 70], [0, 1]]
 g := ![![[20, 37], [41, 6], [18, 64], [20], [32], [1]], ![[21, 34], [45, 65], [37, 7], [20], [32], [1]]]
 h' := ![![[48, 70], [70, 26], [29, 19], [31, 8], [57, 34], [45, 48], [0, 1]], ![[0, 1], [40, 45], [18, 52], [60, 63], [56, 37], [6, 23], [48, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [23, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [26, 23, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9439, -9375, 5300]
  a := ![-5, 0, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5209, -1625, 5300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34061610560381579077627, -1942736174686549448082, 838855053370246183584]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-34061610560381579077627, -1942736174686549448082, 838855053370246183584]] 
 ![![71, 0, 0], ![21, 1, 0], ![45, 0, 1]] where
  M :=![![![-34061610560381579077627, -1942736174686549448082, 838855053370246183584], ![-84989386458340921622898, -26511915080049363425371, -10817561994749050504908], ![179748055493414702606358, -30067451372732637786498, -28454651254735912873453]]]
  hmulB := by decide  
  f := ![![![429130778449340838906304538922003248927443879, -80502113856646390616548500656797909764015978, 43255322948535613061822742164465377181496120]], ![![65478412136260359623878807639763351785129431, -12283319802864969668800130920993865654696149, 6600062277857818924800131319400716048011532]], ![![375095274053525298956262882873889557896480487, -70365408344886468862267044618789687112384572, 37808677518501655684904001621779376154425611]]]
  g := ![![![-436797581600353787735, -1942736174686549448082, 838855053370246183584], ![13500719999808492718743, -26511915080049363425371, -10817561994749050504908], ![29459490715266425006031, -30067451372732637786498, -28454651254735912873453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-429130778449340838906304538922003248927443879, 80502113856646390616548500656797909764015978, -43255322948535613061822742164465377181496120]] ![![-34061610560381579077627, -1942736174686549448082, 838855053370246183584]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136408172578384608680254713855422034, -12174569737646415648199250436890555, -15251160003310340754078424470081388]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![136408172578384608680254713855422034, -12174569737646415648199250436890555, -15251160003310340754078424470081388]] 
 ![![73, 0, 0], ![0, 73, 0], ![26, 51, 1]] where
  M :=![![![136408172578384608680254713855422034, -12174569737646415648199250436890555, -15251160003310340754078424470081388], ![1497690270590077319005564772101166857, -852267451408458106451106375310458, -88298578429188834643273927091424718], ![1434049804076650260482902160303385765, 119196272410837370477383113119205825, -13026837189054873754650356812201013]]]
  hmulB := by decide  
  f := ![![![-144328270647483692765026235106825773163992244979485860782619563173648, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682]], ![![1467320435370089166492944945542462623648280854837998603926630702368673, -275259670674708534657315195626221444285752613764264015604183917168786, 147902277087337118300788394472506373284416303812102499245251922311248]], ![![939980790343758514433394339374500492229479855975901490729129768052320, -176334218861550737428960320758713823208562028540810132511154898048047, 94747742864449098554104141167735368434687658327734229978351764320045]]]
  g := ![![![7300525104992513264195804795582714, 10488145074399739216572608185441921, -15251160003310340754078424470081388], ![51965113832177904379872422965454925, 61676373047085234365760536647771920, -88298578429188834643273927091424718], ![24284213301261328467175499142748111, 10733766699351177150199333021115856, -13026837189054873754650356812201013]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [60, 34, 1] where
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
 g := ![![[3, 50], [69], [69], [67, 57], [61], [1]], ![[55, 23], [69], [69], [27, 16], [61], [1]]]
 h' := ![![[39, 72], [20, 59], [46, 19], [68, 19], [13, 35], [13, 39], [0, 1]], ![[0, 1], [58, 14], [57, 54], [6, 54], [64, 38], [1, 34], [39, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [32, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [60, 34, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36612, -11640, 5440]
  a := ![4, -10, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1436, -3960, 5440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-144328270647483692765026235106825773163992244979485860782619563173648, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-144328270647483692765026235106825773163992244979485860782619563173648, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682]] 
 ![![73, 0, 0], ![58, 1, 0], ![60, 0, 1]] where
  M :=![![![-144328270647483692765026235106825773163992244979485860782619563173648, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682], ![1467320435370089166492944945542462623648280854837998603926630702368673, -275259670674708534657315195626221444285752613764264015604183917168786, 147902277087337118300788394472506373284416303812102499245251922311248], ![-2462209471945599925611723335549587771046495741030487596683584110468115, 461894315680917887587045685994318290316518465156913699374079199124625, -248184635604092628979548815797111202976835815558825114714761108746631]]]
  hmulB := by decide  
  f := ![![![136408172578384608680254713855422034, -12174569737646415648199250436890555, -15251160003310340754078424470081388]], ![![128895401097758693458360796927611573, -9684620715546583091808323722122776, -13326929570153268470956473237755414]], ![![131760824092872969606824451940119285, -8373670025314350252254409768414075, -12713649827228429027388435959138141]]]
  g := ![![![-11531565815913798303107988973505688971727361858398462286192421347366, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682], ![117236228894013110665341405801546904043245948279988514441838117253197, -275259670674708534657315195626221444285752613764264015604183917168786, 147902277087337118300788394472506373284416303812102499245251922311248], ![-196726049934154515984759509251964060695813942282218839417733029245185, 461894315680917887587045685994318290316518465156913699374079199124625, -248184635604092628979548815797111202976835815558825114714761108746631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![136408172578384608680254713855422034, -12174569737646415648199250436890555, -15251160003310340754078424470081388]] ![![-144328270647483692765026235106825773163992244979485860782619563173648, 27075035070615905677766379829110241308916798205438900889422808422155, -14547933336358315765809884502155074569084485420530906091284928221682]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3552424306745367506374680465463312003109370929261810814710052829, -666411453967740845085647827691410402129182791257449306926212770, 358075599223509018511933530418134702662400657243377727349464958]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![3552424306745367506374680465463312003109370929261810814710052829, -666411453967740845085647827691410402129182791257449306926212770, 358075599223509018511933530418134702662400657243377727349464958]] 
 ![![79, 0, 0], ![40, 1, 0], ![10, 0, 1]] where
  M :=![![![3552424306745367506374680465463312003109370929261810814710052829, -666411453967740845085647827691410402129182791257449306926212770, 358075599223509018511933530418134702662400657243377727349464958], ![-36115895777095133677767067339086745965706847858351844314523243612, 6775104699756948672982082239226524327070976844452210360855237451, -3640393124582936052001953435730327710112696090301318114207811662], ![60603599954453708385800131985177609270853086475836815475453089860, -11368837074062302883449833405494714159098654979967709672577889300, 6108693245789207827896434411535113924941794053194761053929024681]]]
  hmulB := by decide  
  f := ![![![-215342767274295608439436790488469, 88311216270103252795783234226970, 65250704025478739105890205581682]], ![![-189686318648406534889428085289852, 49422306579229660194239296567411, 40571470413484149621724023217858]], ![![-150316438529941255667914698444050, 8850032262655452107994029956800, 14085212980758274523648865187221]]]
  g := ![![![337064892066074824363053902138460519767755392495265896433720431, -666411453967740845085647827691410402129182791257449306926212770, 358075599223509018511933530418134702662400657243377727349464958], ![-3426786740779034431354820538618284075283784313081355412742463608, 6775104699756948672982082239226524327070976844452210360855237451, -3640393124582936052001953435730327710112696090301318114207811662], ![5750255069101946144871254735311582739055460065096172048598460950, -11368837074062302883449833405494714159098654979967709672577889300, 6108693245789207827896434411535113924941794053194761053929024681]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44630679611292, -28179157590049, -14176854315198]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-44630679611292, -28179157590049, -14176854315198]] 
 ![![79, 0, 0], ![54, 1, 0], ![54, 0, 1]] where
  M :=![![![-44630679611292, -28179157590049, -14176854315198], ![1375329419614553, -172222368448074, -183251799855492], ![3002389416142821, -40959603582471, -200401526038123]]]
  hmulB := by decide  
  f := ![![![27007704377038645909965644370, -5066467850717622583357743769, 2722309919481329863885170456]], ![![14985327676971108861141204773, -2811148990966848162232733988, 1510484031229967177386555854]], ![![24293186136568500847244099649, -4557242068195318616579941953, 2448693182957529174068020751]]]
  g := ![![![28387265357874, -28179157590049, -14176854315198], ![260391576050723, -172222368448074, -183251799855492], ![202985954628543, -40959603582471, -200401526038123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1897619613332358882, -200343972115276159, -8158788875537966]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-1897619613332358882, -200343972115276159, -8158788875537966]] 
 ![![79, 0, 0], ![63, 1, 0], ![76, 0, 1]] where
  M :=![![![-1897619613332358882, -200343972115276159, -8158788875537966], ![607376126562982475, -1971048713212200576, -1210222621567194920], ![19956435072545409231, -1680713915904415941, -2171392685327476735]]]
  hmulB := by decide  
  f := ![![![2245882756882799539942376078491379640, -421312845600519816987451703771544859, 226379436834035385754409724086843864]], ![![1501996665714510734299945298184656075, -281764703600552284284523971421953819, 151397555490824630207057115429477698]], ![![2645586958038401216848888035157280199, -496294726943730572534804312428911025, 266668633445256803950376593950652699]]]
  g := ![![![143596437778112969, -200343972115276159, -8158788875537966], ![2743802079722005477, -1971048713212200576, -1210222621567194920], ![3681863998220403106, -1680713915904415941, -2171392685327476735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![3552424306745367506374680465463312003109370929261810814710052829, -666411453967740845085647827691410402129182791257449306926212770, 358075599223509018511933530418134702662400657243377727349464958]] ![![-44630679611292, -28179157590049, -14176854315198]]
  ![![2245882756882799539942376078491379640, -421312845600519816987451703771544859, 226379436834035385754409724086843864]] where
 M := ![![![2245882756882799539942376078491379640, -421312845600519816987451703771544859, 226379436834035385754409724086843864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![2245882756882799539942376078491379640, -421312845600519816987451703771544859, 226379436834035385754409724086843864]] ![![-1897619613332358882, -200343972115276159, -8158788875537966]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB136I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB136I1 : PrimesBelowBoundCertificateInterval O 31 79 136 where
  m := 11
  g := ![1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB136I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
      exact NI79N1
      exact NI79N2
  β := ![I43N1, I47N1, I53N1, I59N1, I67N1, I71N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [], [I43N1], [I47N1], [I53N1], [I59N1], [], [I67N1], [I71N1], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
