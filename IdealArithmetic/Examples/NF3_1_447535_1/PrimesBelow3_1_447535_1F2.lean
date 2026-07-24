
import IdealArithmetic.Examples.NF3_1_447535_1.RI3_1_447535_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [73, 20, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 60, 38], [58, 22, 45], [0, 1]]
 g := ![![[56, 40, 9], [37, 32, 11], [77, 65], [9, 51], [21, 37, 1], []], ![[26, 78, 43, 23], [61, 49, 25, 64], [17, 27], [49, 51], [30, 60, 79, 49], [54, 33]], ![[51, 13, 69, 66], [48, 52, 13, 58], [76, 61], [33, 38], [81, 18, 6, 67], [47, 33]]]
 h' := ![![[62, 60, 38], [38, 35, 80], [17, 68, 54], [34, 80, 56], [44, 33, 47], [0, 0, 1], [0, 1]], ![[58, 22, 45], [12, 41, 19], [20, 57, 37], [4, 47, 39], [57, 14, 47], [68, 50, 22], [62, 60, 38]], ![[0, 1], [28, 7, 67], [11, 41, 75], [9, 39, 71], [54, 36, 72], [16, 33, 60], [58, 22, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 28], []]
 b := ![[], [18, 13, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [73, 20, 46, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7564039, -661842, -220697]
  a := ![0, -2, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91133, -7974, -2659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11732571245, -856370646, -68498748]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![11732571245, -856370646, -68498748]] 
 ![![89, 0, 0], ![0, 89, 0], ![63, 61, 1]] where
  M :=![![![11732571245, -856370646, -68498748], ![-8767839744, 10396709363, -6850965168], ![-108519462720, -7090574490, 11253080009]]]
  hmulB := by decide  
  f := ![![![-768738465618641123, -113735987325424206, -73922775745270068]], ![![-9462115295394568704, -1399933883160955805, -909887898603393648]], ![![-7179719082233405157, -1062250004466542917, -690410051489826499]]]
  g := ![![![180314521, 37326438, -68498748], ![4751044560, 4812422299, -6850965168], ![-9184983183, -7792454551, 11253080009]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [45, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 88], [0, 1]]
 g := ![![[51, 2], [39], [55], [37, 87], [76, 5], [1]], ![[0, 87], [39], [55], [88, 2], [82, 84], [1]]]
 h' := ![![[19, 88], [30, 64], [70, 67], [26, 12], [51, 40], [44, 19], [0, 1]], ![[0, 1], [0, 25], [8, 22], [76, 77], [10, 49], [49, 70], [19, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [36, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [45, 70, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![936, 1809, 1388]
  a := ![-1, 1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-972, -931, 1388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-768738465618641123, -113735987325424206, -73922775745270068]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-768738465618641123, -113735987325424206, -73922775745270068]] 
 ![![89, 0, 0], ![46, 1, 0], ![19, 0, 1]] where
  M :=![![![-768738465618641123, -113735987325424206, -73922775745270068], ![-9462115295394568704, -1399933883160955805, -909887898603393648], ![-13375441965729977280, -1978916323202290530, -1286197895835531599]]]
  hmulB := by decide  
  f := ![![![11732571245, -856370646, -68498748]], ![![5965510534, -325801577, -112380984]], ![![1285386415, -262490076, 111815773]]]
  g := ![![![65928648207988805, -113735987325424206, -73922775745270068], ![811491161836785142, -1399933883160955805, -909887898603393648], ![1147106392387084129, -1978916323202290530, -1286197895835531599]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![11732571245, -856370646, -68498748]] ![![-768738465618641123, -113735987325424206, -73922775745270068]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-956998060856069741913969675613099, -141589271498712563069588761198878, -92026035128072420688637601525880]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-956998060856069741913969675613099, -141589271498712563069588761198878, -92026035128072420688637601525880]] 
 ![![97, 0, 0], ![0, 97, 0], ![66, 12, 1]] where
  M :=![![![-956998060856069741913969675613099, -141589271498712563069588761198878, -92026035128072420688637601525880], ![-11779332496393269848145612995312640, -1742769578251289249804021647493137, -1132714171989700504556710089591024], ![-16651010189786049341889159809042304, -2463541462540146672505322952806226, -1601180306752576686734432886294259]]]
  hmulB := by decide  
  f := ![![![23340113406143453, 3340039772830026, -3704272689894696]], ![![-474146904306521088, 750244349710607, 26720318182640208]], ![![-37757957865074502, 1995437861595918, 758474486964053]]]
  g := ![![![52749693377285670345733113660773, 9924980928228417373134664506306, -92026035128072420688637601525880], ![649276318092030551057703638326752, 122162891604382647472953602346383, -1132714171989700504556710089591024], ![917802990266845484356530007076070, 172686826994750242972246099821906, -1601180306752576686734432886294259]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [36, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 96], [0, 1]]
 g := ![![[10, 62], [1], [27], [91], [8], [28, 1]], ![[0, 35], [1], [27], [91], [8], [56, 96]]]
 h' := ![![[28, 96], [60, 81], [22, 96], [86, 30], [89, 24], [59, 69], [0, 1]], ![[0, 1], [0, 16], [91, 1], [53, 67], [82, 73], [51, 28], [28, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [54, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [36, 69, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-300, 16, 66]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -8, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23340113406143453, 3340039772830026, -3704272689894696]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![23340113406143453, 3340039772830026, -3704272689894696]] 
 ![![97, 0, 0], ![1, 1, 0], ![24, 0, 1]] where
  M :=![![![23340113406143453, 3340039772830026, -3704272689894696], ![-474146904306521088, 750244349710607, 26720318182640208], ![486793453960558464, -35888084628504954, -2589795423119419]]]
  hmulB := by decide  
  f := ![![![-956998060856069741913969675613099, -141589271498712563069588761198878, -92026035128072420688637601525880]], ![![-131302376878859171031542089390987, -19426379894329915596635158852495, -12626187702245081703560285475432]], ![![-408442924230223949977571464162440, -60429731737208744187375806408034, -39276341750786750342904487865107]]]
  g := ![![![1122707404028723, 3340039772830026, -3704272689894696], ![-11507059639583471, 750244349710607, 26720318182640208], ![6029243595298242, -35888084628504954, -2589795423119419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-956998060856069741913969675613099, -141589271498712563069588761198878, -92026035128072420688637601525880]] ![![23340113406143453, 3340039772830026, -3704272689894696]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [32, 14, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 62, 9], [50, 38, 92], [0, 1]]
 g := ![![[50, 1, 65], [2, 77], [35, 33, 65], [38, 6], [20, 13], [1]], ![[28, 80, 57, 52], [54, 65], [46, 46, 35, 17], [86, 76], [45, 47], [82, 100, 55, 22]], ![[49, 60, 38, 19], [22, 68], [17, 16, 67, 88], [9, 43], [76, 71], [94, 60, 5, 79]]]
 h' := ![![[16, 62, 9], [17, 45, 41], [92, 33, 73], [93, 63, 60], [81, 99, 39], [69, 87, 66], [0, 1]], ![[50, 38, 92], [20, 18, 44], [43, 5, 41], [0, 12, 19], [5, 82, 50], [58, 40, 59], [16, 62, 9]], ![[0, 1], [46, 38, 16], [12, 63, 88], [10, 26, 22], [46, 21, 12], [85, 75, 77], [50, 38, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 56], []]
 b := ![[], [2, 56, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [32, 14, 35, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10918302, -1019696, -318958]
  a := ![1, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108102, -10096, -3158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀


def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 2, -4]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![45, 2, -4]] 
 ![![103, 0, 0], ![64, 1, 0], ![98, 0, 1]] where
  M :=![![![45, 2, -4], ![-512, 19, 16], ![320, -50, 17]]]
  hmulB := by decide  
  f := ![![![1123, 166, 108]], ![![832, 123, 80]], ![![1258, 186, 121]]]
  g := ![![![3, 2, -4], ![-32, 19, 16], ![18, -50, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54991, -8136, -5288]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-54991, -8136, -5288]] 
 ![![103, 0, 0], ![77, 1, 0], ![99, 0, 1]] where
  M :=![![![-54991, -8136, -5288], ![-676864, -100143, -65088], ![-956800, -141560, -92007]]]
  hmulB := by decide  
  f := ![![![279, -328, 216]], ![![477, -231, 136]], ![![-173, -304, 225]]]
  g := ![![![10631, -8136, -5288], ![130853, -100143, -65088], ![184971, -141560, -92007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![45, 2, -4]] ![![45, 2, -4]]
  ![![-279, 328, -216]] where
 M := ![![![-279, 328, -216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-279, 328, -216]] ![![-54991, -8136, -5288]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-97476467089, -14421786760, -9373449280]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-97476467089, -14421786760, -9373449280]] 
 ![![107, 0, 0], ![0, 107, 0], ![98, 22, 1]] where
  M :=![![![-97476467089, -14421786760, -9373449280], ![-1199801507840, -177512398809, -115374294080], ![-1696013516800, -250927695800, -163090612049]]]
  hmulB := by decide  
  f := ![![![-72763, -40680, 32960]], ![![4218880, 117277, -325440]], ![![747198, -10878, -35249]]]
  g := ![![![7674033293, 1792468200, -9373449280], ![94456816000, 22062823093, -115374294080], ![133522116486, 31187530554, -163090612049]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [98, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 106], [0, 1]]
 g := ![![[36, 19], [33, 9], [9], [47, 3], [3], [3, 1]], ![[93, 88], [60, 98], [9], [56, 104], [3], [6, 106]]]
 h' := ![![[3, 106], [83, 74], [106, 104], [102, 3], [7, 18], [27, 18], [0, 1]], ![[0, 1], [91, 33], [97, 3], [4, 104], [61, 89], [81, 89], [3, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [50, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [98, 104, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4178, 3816, 47]
  a := ![0, -2, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, 26, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![72763, 40680, -32960]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![72763, 40680, -32960]] 
 ![![107, 0, 0], ![38, 1, 0], ![2, 0, 1]] where
  M :=![![![72763, 40680, -32960], ![-4218880, -117277, 325440], ![5734400, -242600, -157957]]]
  hmulB := by decide  
  f := ![![![97476467089, 14421786760, 9373449280]], ![![45830908946, 6780750427, 4407152960]], ![![17672583654, 2614684760, 1699415987]]]
  g := ![![![-13151, 40680, -32960], ![-3862, -117277, 325440], ![142702, -242600, -157957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-97476467089, -14421786760, -9373449280]] ![![72763, 40680, -32960]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11957744628728319538448526842136241740377374747512960612456229, -1769165915795854888034300078635049202372511784812613167384780, -1149870488004439954678473107575111998255483321207991576528528]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-11957744628728319538448526842136241740377374747512960612456229, -1769165915795854888034300078635049202372511784812613167384780, -1149870488004439954678473107575111998255483321207991576528528]] 
 ![![109, 0, 0], ![0, 109, 0], ![96, 91, 1]] where
  M :=![![![-11957744628728319538448526842136241740377374747512960612456229, -1769165915795854888034300078635049202372511784812613167384780, -1149870488004439954678473107575111998255483321207991576528528], ![-147183422464568314198844557769614335776701865114622921795651584, -21776003960555254109232138673797074930538269780781514815540705, -14153327326366839104274400629080393618980094278500905339078240], ![-208055309413798386393534840344084505931593775316686620200795392, -30782089218642023491095670271647136388695315633016157396149908, -20006838044759399221197838595162025728165757995968901648155925]]]
  hmulB := by decide  
  f := ![![![179481442377805480119619783255, 466461794445579014374262249964, -340301993775114292073646123440]], ![![-43558655203214629385426703800320, -1736170719602415550021640830861, 3731694355564632114994097999712]], ![![-35609683150778220233662960006112, -1058631216113091791234849925111, 2795528095779106017073366853603]]]
  g := ![![![903025891923834092758576986101601010019715817325268171874151, 943752738464295238419328006520184794852077710505638718318452, -1149870488004439954678473107575111998255483321207991576528528], ![11115009182262827888178879840569756437113643904784073309686784, 11616300759071808297061819436445126095382112931768815330647515, -14153327326366839104274400629080393618980094278500905339078240], ![15711937090670678337995024447628164807085495342168146220386912, 16420552044536360602182638916404561512609070293579393509963663, -20006838044759399221197838595162025728165757995968901648155925]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [64, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 108], [0, 1]]
 g := ![![[23, 46], [29], [83, 46], [102, 81], [106], [54, 1]], ![[0, 63], [29], [60, 63], [7, 28], [106], [108, 108]]]
 h' := ![![[54, 108], [75, 41], [29, 47], [12, 68], [17, 9], [32, 18], [0, 1]], ![[0, 1], [0, 68], [60, 62], [87, 41], [67, 100], [23, 91], [54, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [26, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [64, 55, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![403944, 359116, 150404]
  a := ![1, 20, 141]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-128760, -122272, 150404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179481442377805480119619783255, 466461794445579014374262249964, -340301993775114292073646123440]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![179481442377805480119619783255, 466461794445579014374262249964, -340301993775114292073646123440]] 
 ![![109, 0, 0], ![35, 1, 0], ![6, 0, 1]] where
  M :=![![![179481442377805480119619783255, 466461794445579014374262249964, -340301993775114292073646123440], ![-43558655203214629385426703800320, -1736170719602415550021640830861, 3731694355564632114994097999712], ![65151941589435942513083905970432, -2179599339282775572558502225292, -2202632514047994564395903080825]]]
  hmulB := by decide  
  f := ![![![-11957744628728319538448526842136241740377374747512960612456229, -1769165915795854888034300078635049202372511784812613167384780, -1149870488004439954678473107575111998255483321207991576528528]], ![![-5189949398807885303160944928847548593485412672271344433317611, -767860651499175919178281114000218321225469561919476841045945, -499071508316717775394687700864305628971761564410831289152080]], ![![-2566988781524479849763541297219284003429890126621691595188374, -379789768013001402011940098563829647733306296714604003673932, -246844596080605861919896121473510988235767503882723404654377]]]
  g := ![![![-129402471564832791472822772705, 466461794445579014374262249964, -340301993775114292073646123440], ![-47549047252457594721411584573, -1736170719602415550021640830861, 3731694355564632114994097999712], ![1418841408702945458156026626978, -2179599339282775572558502225292, -2202632514047994564395903080825]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-11957744628728319538448526842136241740377374747512960612456229, -1769165915795854888034300078635049202372511784812613167384780, -1149870488004439954678473107575111998255483321207991576528528]] ![![179481442377805480119619783255, 466461794445579014374262249964, -340301993775114292073646123440]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31178314207291829815395491103621741489116109925656185585453981268367131955780908059143421368908443001661450950987, -4612877471475193201372697142278497499308139306499439805756406083271135780725008259828981037575843449604983302082, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-31178314207291829815395491103621741489116109925656185585453981268367131955780908059143421368908443001661450950987, -4612877471475193201372697142278497499308139306499439805756406083271135780725008259828981037575843449604983302082, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606]] 
 ![![113, 0, 0], ![0, 113, 0], ![4, 4, 1]] where
  M :=![![![-31178314207291829815395491103621741489116109925656185585453981268367131955780908059143421368908443001661450950987, -4612877471475193201372697142278497499308139306499439805756406083271135780725008259828981037575843449604983302082, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606], ![-383762250673930698566694761363978792954817384362655279883442129029198656769384316495509889937558992155585203917568, -56778189762497608094634308007992829228140824939488336009836128782922569278581621127320599512444543834775000092311, -36903019771801545610981577138227979994465114451995518446051248666169086245800066078631848300606747596839866416656], ![-542478035014583392454868389041150330792089658186596385151389712530055547836628017696170836567513087529989712176800, -80260423634567689730445725166446831614509148190827988625725108711547782561248097380741603505225778166683033604270, -52165312291022414893261610865714331728832685632988896204079722699651433497856612867491618474868700385170016790229]]]
  hmulB := by decide  
  f := ![![![93859864775122327465540898173257056080891041123737326477, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298]], ![![1536249323481709550581103128681864771282756934473647142144, 153282270528047040132322990358266764030994800995212775529, -196729832999850227044975881318238173835376079860417032272]], ![![28148037695526638811011717834012773731665752281536809428, 4731475461704493735974230227484271358501608061787465270, -4964938415819196161161938734323875092730100480191165941]]]
  g := ![![![-169785344015322968895453803637145169993611209418789452115897475541634282581749098837687940781944464573446135651, 65307016478629567511827558852618051155131893405606528235408499547710816312550899386333655070556416418204020534, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606], ![-2089824527316146160378481883283777636964220588979408903533071985526746122001628780362676962257805325382528657088, 803839728537244020790194695087779564156810910340652546675830671519944917739987992807139767167986252677738633401, -36903019771801545610981577138227979994465114451995518446051248666169086245800066078631848300606747596839866416656], ![-2954130848234457813113468544940646052006716067740184073761688687888936405709748373683224448389719345038138451468, 1136290491411698848164608126516907038060368091514403506111449399000512844514852691055087348621672773221212686342, -52165312291022414893261610865714331728832685632988896204079722699651433497856612867491618474868700385170016790229]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [94, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 112], [0, 1]]
 g := ![![[76, 4], [56], [11], [98], [10, 26], [88, 1]], ![[89, 109], [56], [11], [98], [38, 87], [63, 112]]]
 h' := ![![[88, 112], [69, 111], [19, 13], [107, 89], [77, 95], [90, 79], [0, 1]], ![[0, 1], [6, 2], [33, 100], [29, 24], [75, 18], [36, 34], [88, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [107, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [94, 25, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4022, 3118, 1514]
  a := ![-1, 2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -26, 1514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93859864775122327465540898173257056080891041123737326477, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![93859864775122327465540898173257056080891041123737326477, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298]] 
 ![![113, 0, 0], ![81, 1, 0], ![102, 0, 1]] where
  M :=![![![93859864775122327465540898173257056080891041123737326477, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298], ![1536249323481709550581103128681864771282756934473647142144, 153282270528047040132322990358266764030994800995212775529, -196729832999850227044975881318238173835376079860417032272], ![-3339708493432817326542251992177043877776361894575878409120, 19892561560344745158283994931774694304390546931340989530, 177873499653028318512944975523046535760416810977764904563]]]
  hmulB := by decide  
  f := ![![![-31178314207291829815395491103621741489116109925656185585453981268367131955780908059143421368908443001661450950987, -4612877471475193201372697142278497499308139306499439805756406083271135780725008259828981037575843449604983302082, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606]], ![![-25745183198801494810740969387233096049320551224254923117745262051034834913164936896337407263886220135311174610155, -3809037742937949180582502447190717935151328396158787259080575411751190862985020267021841270407857196927244668681, -2475686451561047042457682352335139910718455668088392148206123636658927975510407777530501774572728294869877241334]], ![![-32943947647419026846240783023102371351167547527464843494404387627464628383418412740962830231824551094685466452898, -4874105537389711471420007377688969703928666880121865918698040081461979045975211857374315657858069115277799384218, -3167927927405406551447756626793229489953122024752033826205289108582248788592564071458858955919124090788955541257]]]
  g := ![![![7624342869461226355545178237628828111045370951785594795, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298], ![81299366165439136800446732779845580672394143359503978903, 153282270528047040132322990358266764030994800995212775529, -196729832999850227044975881318238173835376079860417032272], ![-204372592428580797988350823761075581982252308988907246252, 19892561560344745158283994931774694304390546931340989530, 177873499653028318512944975523046535760416810977764904563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-31178314207291829815395491103621741489116109925656185585453981268367131955780908059143421368908443001661450950987, -4612877471475193201372697142278497499308139306499439805756406083271135780725008259828981037575843449604983302082, -2998142583390083582552302823156084319959510815333244374089391633040614506010814972621171015137179626215509405606]] ![![93859864775122327465540898173257056080891041123737326477, -24591229124981278380621985164779771729422009982552129034, 12001947839700855863914868192827068525646538550575368298]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [37, 121, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 91, 5], [124, 35, 122], [0, 1]]
 g := ![![[125, 39, 11], [37, 86, 18], [38, 43, 72], [51, 4, 4], [46, 115, 88], [1]], ![[16, 56, 103, 67], [119, 83, 45, 23], [2, 53, 47, 119], [9, 97, 71, 78], [72, 28, 64, 77], [60, 107, 79, 125]], ![[50, 30, 50, 100], [118, 86, 96, 19], [17, 69, 18, 81], [48, 33, 49, 41], [50, 24, 10, 88], [15, 69, 100, 2]]]
 h' := ![![[74, 91, 5], [28, 42, 97], [118, 104, 48], [18, 92, 96], [76, 57, 2], [90, 6, 71], [0, 1]], ![[124, 35, 122], [60, 85, 49], [61, 0, 41], [83, 112, 10], [71, 9, 101], [33, 115, 102], [74, 91, 5]], ![[0, 1], [105, 0, 108], [40, 23, 38], [83, 50, 21], [10, 61, 24], [53, 6, 81], [124, 35, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 3], []]
 b := ![[], [74, 37, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [37, 121, 56, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28364053, 3573018, 1260094]
  a := ![0, 3, 23]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223339, 28134, 9922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48214887875, -7133463618, -4636399118]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-48214887875, -7133463618, -4636399118]] 
 ![![131, 0, 0], ![0, 131, 0], ![68, 85, 1]] where
  M :=![![![-48214887875, -7133463618, -4636399118], ![-593459087104, -87803145319, -57067708944], ![-838900957216, -124116631214, -80669681701]]]
  hmulB := by decide  
  f := ![![![-310913, 22786, 1750]], ![![224000, -275877, 182288]], ![![6004, -165745, 116907]]]
  g := ![![![2038627879, 2953896652, -4636399118], ![25092710848, 36358413091, -57067708944], ![35470514492, 51395468041, -80669681701]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [124, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 130], [0, 1]]
 g := ![![[12, 4], [49, 74], [129], [61], [105], [113], [1]], ![[86, 127], [108, 57], [129], [61], [105], [113], [1]]]
 h' := ![![[84, 130], [81, 129], [39, 104], [61, 28], [114, 42], [54, 57], [7, 84], [0, 1]], ![[0, 1], [44, 2], [129, 27], [55, 103], [105, 89], [126, 74], [120, 47], [84, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [87, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [124, 47, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64158, 52360, 18170]
  a := ![2, -8, -54]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8942, -11390, 18170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-310913, 22786, 1750]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-310913, 22786, 1750]] 
 ![![131, 0, 0], ![106, 1, 0], ![56, 0, 1]] where
  M :=![![![-310913, 22786, 1750], ![224000, -275877, 182288], ![2888608, 187502, -298663]]]
  hmulB := by decide  
  f := ![![![-48214887875, -7133463618, -4636399118]], ![![-43543795434, -6442368617, -4187221492]], ![![-27014768536, -3996874762, -2597771239]]]
  g := ![![![-21559, 22786, 1750], ![147014, -275877, 182288], ![-1996, 187502, -298663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-48214887875, -7133463618, -4636399118]] ![![-310913, 22786, 1750]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [104, 114, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 74, 13], [60, 62, 124], [0, 1]]
 g := ![![[33, 55, 25], [67, 105], [114, 120], [75, 25, 9], [125, 107], [53, 1], []], ![[63, 55, 31, 110], [77, 88], [84, 63], [112, 2, 67, 58], [122, 38], [84, 8], [58, 32]], ![[43, 80, 26, 42], [123, 101], [61, 36], [77, 62, 105, 55], [103, 88], [101, 133], [84, 32]]]
 h' := ![![[130, 74, 13], [68, 127, 132], [7, 131, 70], [9, 45, 95], [80, 121, 134], [105, 19, 92], [0, 0, 1], [0, 1]], ![[60, 62, 124], [50, 25, 108], [48, 80, 15], [133, 29, 36], [57, 97, 17], [2, 71, 60], [45, 121, 62], [130, 74, 13]], ![[0, 1], [77, 122, 34], [26, 63, 52], [43, 63, 6], [6, 56, 123], [13, 47, 122], [70, 16, 74], [60, 62, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 99], []]
 b := ![[], [104, 9, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [104, 114, 84, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17947, 2192, 3699]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![131, 16, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB190I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB190I2 : PrimesBelowBoundCertificateInterval O 79 137 190 where
  m := 11
  g := ![1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB190I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I97N1, I103N0, I103N1, I107N1, I109N1, I113N1, I131N1]
  Il := ![[], [I89N1], [I97N1], [], [I103N0, I103N0, I103N1], [I107N1], [I109N1], [I113N1], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
