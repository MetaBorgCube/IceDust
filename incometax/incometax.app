application incometax

imports lib/icedust/newcrud-ui

imports lib/icedust/non-required-inputs

imports lib/icedust/Expressions

section  data

  init
  {
    var phdStudent := Income{} ;
    var phpProgrammer := Income{} ;
    var seniorDeveloper := Income{} ;
    phdStudent.monthlySalary := 2500.0;
    phdStudent.name := "PhD Student";
    phdStudent.thirteenthMonth := true;
    phpProgrammer.holidayAllowance := 0.0;
    phpProgrammer.monthlySalary := 2800.0;
    phpProgrammer.name := "PHP programmer";
    seniorDeveloper.leaseCarPercent := 21.0;
    seniorDeveloper.leaseCarPrice := 17000.0;
    seniorDeveloper.monthlySalary := 4000.0;
    seniorDeveloper.name := "Senior Developer";
    phdStudent.save();
    phpProgrammer.save();
    seniorDeveloper.save();
  }

section  model

  entity Income {
    employedTaxDiscount : Float := calculateEmployedTaxDiscount()
    function getEmployedTaxDiscount ( ) : Float
    {
      return this.employedTaxDiscount;
    }
    static function getEmployedTaxDiscount ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getEmployedTaxDiscount();
    }
    static function getEmployedTaxDiscount ( entities : List<Income> ) : List<Float>
    {
      return [ en.getEmployedTaxDiscount() | en : Income in entities where en.getEmployedTaxDiscount() != null ];
    }
    function calculateEmployedTaxDiscount ( ) : Float
    {
      return ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 9147.0), Expressions.mul_Float(0.0193, Income.getTaxableIncome(this)), ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 19758.0), Expressions.plus_Float(146.0, Expressions.mul_Float(0.27698, Expressions.minus_Float(Income.getTaxableIncome(this), 9147.0))), ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 34015.0), 3103.0, ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 111590.0), Expressions.minus_Float(3103.0, Expressions.mul_Float(0.04, Expressions.minus_Float(Income.getTaxableIncome(this), 34015.0))), 0.0) as Float )) as Float )) as Float )) as Float );
    }
    gernalTaxDiscount : Float := calculateGernalTaxDiscount()
    function getGernalTaxDiscount ( ) : Float
    {
      return this.gernalTaxDiscount;
    }
    static function getGernalTaxDiscount ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getGernalTaxDiscount();
    }
    static function getGernalTaxDiscount ( entities : List<Income> ) : List<Float>
    {
      return [ en.getGernalTaxDiscount() | en : Income in entities where en.getGernalTaxDiscount() != null ];
    }
    function calculateGernalTaxDiscount ( ) : Float
    {
      return ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 19222.0), 2242.0, ( Expressions.conditional_One_One_One(Expressions.lt_Float(Income.getTaxableIncome(this), 66417.0), Expressions.minus_Float(2242.0, Expressions.mul_Float(0.04822, Expressions.minus_Float(Income.getTaxableIncome(this), 19922.0))), 0.0) as Float )) as Float );
    }
    grossSalary : Float := calculateGrossSalary()
    function getGrossSalary ( ) : Float
    {
      return this.grossSalary;
    }
    static function getGrossSalary ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getGrossSalary();
    }
    static function getGrossSalary ( entities : List<Income> ) : List<Float>
    {
      return [ en.getGrossSalary() | en : Income in entities where en.getGrossSalary() != null ];
    }
    function calculateGrossSalary ( ) : Float
    {
      return Expressions.mul_Float(Income.getMonthlySalary(this), Expressions.plus_Float(Expressions.plus_Float(1.0, Expressions.div_Float(Income.getHolidayAllowance(this), 100.0)), ( Expressions.conditional_One_One_One(Income.getThirteenthMonth(this), Expressions.div_Float(1.0, 12.0), 0.0) as Float )));
    }
    grossSalaryYear : Float := calculateGrossSalaryYear()
    function getGrossSalaryYear ( ) : Float
    {
      return this.grossSalaryYear;
    }
    static function getGrossSalaryYear ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getGrossSalaryYear();
    }
    static function getGrossSalaryYear ( entities : List<Income> ) : List<Float>
    {
      return [ en.getGrossSalaryYear() | en : Income in entities where en.getGrossSalaryYear() != null ];
    }
    function calculateGrossSalaryYear ( ) : Float
    {
      return Expressions.mul_Float(Income.getGrossSalary(this), 12.0);
    }
    holidayAllowance : Float ( default= calculateHolidayAllowance() )
    function getHolidayAllowance ( ) : Float
    {
      return if ( this.holidayAllowance != null ) this.holidayAllowance else this.calculateHolidayAllowance();
    }
    static function getHolidayAllowance ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getHolidayAllowance();
    }
    static function getHolidayAllowance ( entities : List<Income> ) : List<Float>
    {
      return [ en.getHolidayAllowance() | en : Income in entities where en.getHolidayAllowance() != null ];
    }
    function calculateHolidayAllowance ( ) : Float
    {
      return 8.0;
    }
    incomeTax : Float := calculateIncomeTax()
    function getIncomeTax ( ) : Float
    {
      return this.incomeTax;
    }
    static function getIncomeTax ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getIncomeTax();
    }
    static function getIncomeTax ( entities : List<Income> ) : List<Float>
    {
      return [ en.getIncomeTax() | en : Income in entities where en.getIncomeTax() != null ];
    }
    function calculateIncomeTax ( ) : Float
    {
      return Expressions.plus_Float(Expressions.plus_Float(Expressions.plus_Float(Expressions.mul_Float(Income.getSalaryBracket1(this), Income.getTaxRate1(this)), Expressions.mul_Float(Income.getSalaryBracket2(this), Income.getTaxRate2(this))), Expressions.mul_Float(Income.getSalaryBracket3(this), Income.getTaxRate3(this))), Expressions.mul_Float(Income.getSalaryBracket4(this), Income.getTaxRate4(this)));
    }
    leaseCarAddition : Float := calculateLeaseCarAddition()
    function getLeaseCarAddition ( ) : Float
    {
      return this.leaseCarAddition;
    }
    static function getLeaseCarAddition ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getLeaseCarAddition();
    }
    static function getLeaseCarAddition ( entities : List<Income> ) : List<Float>
    {
      return [ en.getLeaseCarAddition() | en : Income in entities where en.getLeaseCarAddition() != null ];
    }
    function calculateLeaseCarAddition ( ) : Float
    {
      return Expressions.div_Float(Expressions.mul_Float(Income.getLeaseCarPrice(this), Income.getLeaseCarPercent(this)), 100.0);
    }
    leaseCarPercent : Float ( default= null )
    function getLeaseCarPercent ( ) : Float
    {
      return this.leaseCarPercent;
    }
    static function getLeaseCarPercent ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getLeaseCarPercent();
    }
    static function getLeaseCarPercent ( entities : List<Income> ) : List<Float>
    {
      return [ en.getLeaseCarPercent() | en : Income in entities where en.getLeaseCarPercent() != null ];
    }
    leaseCarPrice : Float ( default= null )
    function getLeaseCarPrice ( ) : Float
    {
      return this.leaseCarPrice;
    }
    static function getLeaseCarPrice ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getLeaseCarPrice();
    }
    static function getLeaseCarPrice ( entities : List<Income> ) : List<Float>
    {
      return [ en.getLeaseCarPrice() | en : Income in entities where en.getLeaseCarPrice() != null ];
    }
    monthlySalary : Float ( validate ( monthlySalary != null , "" + "monthlySalary" + " cannot be empty! " ) )
    function getMonthlySalary ( ) : Float
    {
      return this.monthlySalary;
    }
    static function getMonthlySalary ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getMonthlySalary();
    }
    static function getMonthlySalary ( entities : List<Income> ) : List<Float>
    {
      return [ en.getMonthlySalary() | en : Income in entities where en.getMonthlySalary() != null ];
    }
    name : String ( default= calculateName() )
    function getName ( ) : String
    {
      return if ( this.name != null ) this.name else this.calculateName();
    }
    static function getName ( en : Income ) : String
    {
      return if ( en == null ) ( null as String ) else en.getName();
    }
    static function getName ( entities : List<Income> ) : List<String>
    {
      return [ en.getName() | en : Income in entities where en.getName() != null ];
    }
    function calculateName ( ) : String
    {
      return "Untitled";
    }
    netSalary : Float := calculateNetSalary()
    function getNetSalary ( ) : Float
    {
      return this.netSalary;
    }
    static function getNetSalary ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getNetSalary();
    }
    static function getNetSalary ( entities : List<Income> ) : List<Float>
    {
      return [ en.getNetSalary() | en : Income in entities where en.getNetSalary() != null ];
    }
    function calculateNetSalary ( ) : Float
    {
      return Expressions.div_Float(Income.getNetSalaryYear(this), 12.0);
    }
    netSalaryYear : Float := calculateNetSalaryYear()
    function getNetSalaryYear ( ) : Float
    {
      return this.netSalaryYear;
    }
    static function getNetSalaryYear ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getNetSalaryYear();
    }
    static function getNetSalaryYear ( entities : List<Income> ) : List<Float>
    {
      return [ en.getNetSalaryYear() | en : Income in entities where en.getNetSalaryYear() != null ];
    }
    function calculateNetSalaryYear ( ) : Float
    {
      return Expressions.minus_Float(Income.getGrossSalaryYear(this), Income.getTax(this));
    }
    salaryBracket1 : Float := calculateSalaryBracket1()
    function getSalaryBracket1 ( ) : Float
    {
      return this.salaryBracket1;
    }
    static function getSalaryBracket1 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getSalaryBracket1();
    }
    static function getSalaryBracket1 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getSalaryBracket1() | en : Income in entities where en.getSalaryBracket1() != null ];
    }
    function calculateSalaryBracket1 ( ) : Float
    {
      return Expressions.min_Float(( Expressions.merge_One_One(Income.getTaxableIncome(this), Income.getTaxBracket1(this)) as List<Float> ));
    }
    salaryBracket2 : Float := calculateSalaryBracket2()
    function getSalaryBracket2 ( ) : Float
    {
      return this.salaryBracket2;
    }
    static function getSalaryBracket2 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getSalaryBracket2();
    }
    static function getSalaryBracket2 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getSalaryBracket2() | en : Income in entities where en.getSalaryBracket2() != null ];
    }
    function calculateSalaryBracket2 ( ) : Float
    {
      return Expressions.max_Float(( Expressions.merge_One_One(0.0, Expressions.minus_Float(Expressions.min_Float(( Expressions.merge_One_One(Income.getTaxableIncome(this), Income.getTaxBracket2(this)) as List<Float> )), Income.getTaxBracket1(this))) as List<Float> ));
    }
    salaryBracket3 : Float := calculateSalaryBracket3()
    function getSalaryBracket3 ( ) : Float
    {
      return this.salaryBracket3;
    }
    static function getSalaryBracket3 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getSalaryBracket3();
    }
    static function getSalaryBracket3 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getSalaryBracket3() | en : Income in entities where en.getSalaryBracket3() != null ];
    }
    function calculateSalaryBracket3 ( ) : Float
    {
      return Expressions.max_Float(( Expressions.merge_One_One(0.0, Expressions.minus_Float(Expressions.min_Float(( Expressions.merge_One_One(Income.getTaxableIncome(this), Income.getTaxBracket3(this)) as List<Float> )), Income.getTaxBracket2(this))) as List<Float> ));
    }
    salaryBracket4 : Float := calculateSalaryBracket4()
    function getSalaryBracket4 ( ) : Float
    {
      return this.salaryBracket4;
    }
    static function getSalaryBracket4 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getSalaryBracket4();
    }
    static function getSalaryBracket4 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getSalaryBracket4() | en : Income in entities where en.getSalaryBracket4() != null ];
    }
    function calculateSalaryBracket4 ( ) : Float
    {
      return Expressions.max_Float(( Expressions.merge_One_One(0.0, Expressions.minus_Float(Income.getTaxableIncome(this), Income.getTaxBracket3(this))) as List<Float> ));
    }
    summary : String := calculateSummary()
    function getSummary ( ) : String
    {
      return this.summary;
    }
    static function getSummary ( en : Income ) : String
    {
      return if ( en == null ) ( null as String ) else en.getSummary();
    }
    static function getSummary ( entities : List<Income> ) : List<String>
    {
      return [ en.getSummary() | en : Income in entities where en.getSummary() != null ];
    }
    function calculateSummary ( ) : String
    {
      return Expressions.plus_String(Expressions.plus_String(Expressions.plus_String(Expressions.plus_String(Expressions.plus_String(Expressions.plus_String(Expressions.plus_String(Income.getName(this), " has a gross salary of "), Expressions.asString(Income.getGrossSalary(this))), " per month and a net salary of "), Expressions.asString(Income.getNetSalary(this))), " per month"), ( Expressions.conditional_One_One_One(Expressions.gt_Integer(Expressions.count(Income.getLeaseCarPrice(this)), 0), " with a lease car", "") as String )), ".");
    }
    tax : Float := calculateTax()
    function getTax ( ) : Float
    {
      return this.tax;
    }
    static function getTax ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTax();
    }
    static function getTax ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTax() | en : Income in entities where en.getTax() != null ];
    }
    function calculateTax ( ) : Float
    {
      return Expressions.minus_Float(Expressions.minus_Float(Income.getIncomeTax(this), Income.getGernalTaxDiscount(this)), Income.getEmployedTaxDiscount(this));
    }
    taxableIncome : Float := calculateTaxableIncome()
    function getTaxableIncome ( ) : Float
    {
      return this.taxableIncome;
    }
    static function getTaxableIncome ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxableIncome();
    }
    static function getTaxableIncome ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxableIncome() | en : Income in entities where en.getTaxableIncome() != null ];
    }
    function calculateTaxableIncome ( ) : Float
    {
      return Expressions.plus_Float(Income.getGrossSalaryYear(this), ( Expressions.choice_One_One(Income.getLeaseCarAddition(this), 0.0) as Float ));
    }
    taxBracket1 : Float := calculateTaxBracket1()
    function getTaxBracket1 ( ) : Float
    {
      return this.taxBracket1;
    }
    static function getTaxBracket1 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxBracket1();
    }
    static function getTaxBracket1 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxBracket1() | en : Income in entities where en.getTaxBracket1() != null ];
    }
    function calculateTaxBracket1 ( ) : Float
    {
      return 19922.0;
    }
    taxBracket2 : Float := calculateTaxBracket2()
    function getTaxBracket2 ( ) : Float
    {
      return this.taxBracket2;
    }
    static function getTaxBracket2 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxBracket2();
    }
    static function getTaxBracket2 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxBracket2() | en : Income in entities where en.getTaxBracket2() != null ];
    }
    function calculateTaxBracket2 ( ) : Float
    {
      return 33715.0;
    }
    taxBracket3 : Float := calculateTaxBracket3()
    function getTaxBracket3 ( ) : Float
    {
      return this.taxBracket3;
    }
    static function getTaxBracket3 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxBracket3();
    }
    static function getTaxBracket3 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxBracket3() | en : Income in entities where en.getTaxBracket3() != null ];
    }
    function calculateTaxBracket3 ( ) : Float
    {
      return 66421.0;
    }
    taxRate1 : Float := calculateTaxRate1()
    function getTaxRate1 ( ) : Float
    {
      return this.taxRate1;
    }
    static function getTaxRate1 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxRate1();
    }
    static function getTaxRate1 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxRate1() | en : Income in entities where en.getTaxRate1() != null ];
    }
    function calculateTaxRate1 ( ) : Float
    {
      return Expressions.div_Float(36.55, 100.0);
    }
    taxRate2 : Float := calculateTaxRate2()
    function getTaxRate2 ( ) : Float
    {
      return this.taxRate2;
    }
    static function getTaxRate2 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxRate2();
    }
    static function getTaxRate2 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxRate2() | en : Income in entities where en.getTaxRate2() != null ];
    }
    function calculateTaxRate2 ( ) : Float
    {
      return Expressions.div_Float(40.15, 100.0);
    }
    taxRate3 : Float := calculateTaxRate3()
    function getTaxRate3 ( ) : Float
    {
      return this.taxRate3;
    }
    static function getTaxRate3 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxRate3();
    }
    static function getTaxRate3 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxRate3() | en : Income in entities where en.getTaxRate3() != null ];
    }
    function calculateTaxRate3 ( ) : Float
    {
      return Expressions.div_Float(40.15, 100.0);
    }
    taxRate4 : Float := calculateTaxRate4()
    function getTaxRate4 ( ) : Float
    {
      return this.taxRate4;
    }
    static function getTaxRate4 ( en : Income ) : Float
    {
      return if ( en == null ) ( null as Float ) else en.getTaxRate4();
    }
    static function getTaxRate4 ( entities : List<Income> ) : List<Float>
    {
      return [ en.getTaxRate4() | en : Income in entities where en.getTaxRate4() != null ];
    }
    function calculateTaxRate4 ( ) : Float
    {
      return Expressions.div_Float(52.0, 100.0);
    }
    thirteenthMonth : Bool ( default= calculateThirteenthMonth() )
    function getThirteenthMonth ( ) : Bool
    {
      return if ( this.thirteenthMonth != null ) this.thirteenthMonth else this.calculateThirteenthMonth();
    }
    static function getThirteenthMonth ( en : Income ) : Bool
    {
      return if ( en == null ) ( null as Bool ) else en.getThirteenthMonth();
    }
    static function getThirteenthMonth ( entities : List<Income> ) : List<Bool>
    {
      return [ en.getThirteenthMonth() | en : Income in entities where en.getThirteenthMonth() != null ];
    }
    function calculateThirteenthMonth ( ) : Bool
    {
      return false;
    }
  }

section  ui

  define

  applicationmenu

  (

  )

  {

  navbaritem
    {
    navigate manageIncome() [ ] { "Income" }
      }

  }

  page manageIncome ( )
  {
  main (  )
    define
    body
    (
    )
    {
    navigate createIncome() [ ] { "Create" }
    <
    br
    />
    for
    (
    entity
    :
    Income
    )
    {
    output ( entity.name )
    navigate income(entity) [ ] { "View" }
    " "
    navigate editIncome(entity) [ ] { "Edit" }
    " "
    submit
    (
    "Remove"
    ,
    removeIncome(entity)
    )
    [
    ]
    <
    br
    />
    }
    action removeIncome ( entity : Income )
    {
      entity.delete();
    }
    }
  }

  page createIncome ( )
  {
  main (  )
    define
    body
    (
    )
    {
    header
      {
      "Create"
        }
    var
    holidayAllowance
    :
    Float
    var
    leaseCarPercent
    :
    Float
    var
    leaseCarPrice
    :
    Float
    var
    monthlySalary
    :
    Float
    var
    name
    :
    String
    var
    thirteenthMonth
    :
    Bool
    form
      {
      ""
        "holidayAllowance"
        ": "
        input ( holidayAllowance )
        ""
        "leaseCarPercent"
        ": "
        input ( leaseCarPercent )
        ""
        "leaseCarPrice"
        ": "
        input ( leaseCarPrice )
        ""
        "monthlySalary"
        ": "
        input ( monthlySalary )
        ""
        "name"
        ": "
        input ( name )
        ""
        "thirteenthMonth"
        ": "
        input ( thirteenthMonth )
        submit
        (
        "Save"
        ,
        save()
        )
        [
        ]
        }
    action save ( )
    {
      if ( name.trim() == "" )
      {
        name := null;
      }
      var temp := Income{holidayAllowance := holidayAllowance,
                         leaseCarPercent := leaseCarPercent,
                         leaseCarPrice := leaseCarPrice,
                         monthlySalary := monthlySalary,
                         name := name,
                         thirteenthMonth := thirteenthMonth} ;
      temp.save();
    }
    navigate manageIncome() [ ] { "Back" }
    }
  }

  page income ( temp : Income )
  {
  main (  )
    define
    body
    (
    )
    {
    header
      {
      "View"
        }
    ""
    "employedTaxDiscount"
    ": "
    output ( temp.getEmployedTaxDiscount() )
    <
    br
    />
    ""
    "gernalTaxDiscount"
    ": "
    output ( temp.getGernalTaxDiscount() )
    <
    br
    />
    ""
    "grossSalary"
    ": "
    output ( temp.getGrossSalary() )
    <
    br
    />
    ""
    "grossSalaryYear"
    ": "
    output ( temp.getGrossSalaryYear() )
    <
    br
    />
    ""
    "holidayAllowance"
    ": "
    output ( temp.getHolidayAllowance() )
    <
    br
    />
    ""
    "incomeTax"
    ": "
    output ( temp.getIncomeTax() )
    <
    br
    />
    ""
    "leaseCarAddition"
    ": "
    output ( temp.getLeaseCarAddition() )
    <
    br
    />
    ""
    "leaseCarPercent"
    ": "
    output ( temp.getLeaseCarPercent() )
    <
    br
    />
    ""
    "leaseCarPrice"
    ": "
    output ( temp.getLeaseCarPrice() )
    <
    br
    />
    ""
    "monthlySalary"
    ": "
    output ( temp.getMonthlySalary() )
    <
    br
    />
    ""
    "name"
    ": "
    output ( temp.getName() )
    <
    br
    />
    ""
    "netSalary"
    ": "
    output ( temp.getNetSalary() )
    <
    br
    />
    ""
    "netSalaryYear"
    ": "
    output ( temp.getNetSalaryYear() )
    <
    br
    />
    ""
    "salaryBracket1"
    ": "
    output ( temp.getSalaryBracket1() )
    <
    br
    />
    ""
    "salaryBracket2"
    ": "
    output ( temp.getSalaryBracket2() )
    <
    br
    />
    ""
    "salaryBracket3"
    ": "
    output ( temp.getSalaryBracket3() )
    <
    br
    />
    ""
    "salaryBracket4"
    ": "
    output ( temp.getSalaryBracket4() )
    <
    br
    />
    ""
    "summary"
    ": "
    output ( temp.getSummary() )
    <
    br
    />
    ""
    "tax"
    ": "
    output ( temp.getTax() )
    <
    br
    />
    ""
    "taxableIncome"
    ": "
    output ( temp.getTaxableIncome() )
    <
    br
    />
    ""
    "taxBracket1"
    ": "
    output ( temp.getTaxBracket1() )
    <
    br
    />
    ""
    "taxBracket2"
    ": "
    output ( temp.getTaxBracket2() )
    <
    br
    />
    ""
    "taxBracket3"
    ": "
    output ( temp.getTaxBracket3() )
    <
    br
    />
    ""
    "taxRate1"
    ": "
    output ( temp.getTaxRate1() )
    <
    br
    />
    ""
    "taxRate2"
    ": "
    output ( temp.getTaxRate2() )
    <
    br
    />
    ""
    "taxRate3"
    ": "
    output ( temp.getTaxRate3() )
    <
    br
    />
    ""
    "taxRate4"
    ": "
    output ( temp.getTaxRate4() )
    <
    br
    />
    ""
    "thirteenthMonth"
    ": "
    output ( temp.getThirteenthMonth() )
    <
    br
    />
    <
    hr
    />
    navigate manageIncome() [ ] { "Back" }
    }
  }

  page editIncome ( temp : Income )
  {
  includeJS ( "Expressions.js" )
    includeJS ( "javascript-lib.js" )
    includeJS ( "derivations.js" )
    main (  )
    define
    body
    (
    )
    {
    header
      {
      "Edit"
        }
    var
    holidayAllowance
    :=
    temp.holidayAllowance
    var
    leaseCarPercent
    :=
    temp.getLeaseCarPercent()
    var
    leaseCarPrice
    :=
    temp.getLeaseCarPrice()
    var
    monthlySalary
    :=
    temp.getMonthlySalary()
    var
    name
    :=
    temp.name
    var
    thirteenthMonth
    :=
    temp.thirteenthMonth
    form
      {
      ""
        "employedTaxDiscount"
        ": "
        <
        div
        data-name
        =
        "employedTaxDiscount"
        data-type
        =
        "Float"
        data-updates
        =
        "tax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getEmployedTaxDiscount() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "gernalTaxDiscount"
        ": "
        <
        div
        data-name
        =
        "gernalTaxDiscount"
        data-type
        =
        "Float"
        data-updates
        =
        "tax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getGernalTaxDiscount() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "grossSalary"
        ": "
        <
        div
        data-name
        =
        "grossSalary"
        data-type
        =
        "Float"
        data-updates
        =
        "summary grossSalaryYear "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getGrossSalary() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "grossSalaryYear"
        ": "
        <
        div
        data-name
        =
        "grossSalaryYear"
        data-type
        =
        "Float"
        data-updates
        =
        "netSalaryYear taxableIncome "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getGrossSalaryYear() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "holidayAllowance"
        ": "
        <
        div
        data-name
        =
        "holidayAllowance"
        data-type
        =
        "Float"
        data-updates
        =
        "grossSalary "
        data-default
        =
        "true"
        >
        ""
        input ( holidayAllowance )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "incomeTax"
        ": "
        <
        div
        data-name
        =
        "incomeTax"
        data-type
        =
        "Float"
        data-updates
        =
        "tax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getIncomeTax() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "leaseCarAddition"
        ": "
        <
        div
        data-name
        =
        "leaseCarAddition"
        data-type
        =
        "Float?"
        data-updates
        =
        "taxableIncome "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getLeaseCarAddition() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "leaseCarPercent"
        ": "
        <
        div
        data-name
        =
        "leaseCarPercent"
        data-type
        =
        "Float?"
        data-updates
        =
        "leaseCarAddition "
        >
        ""
        input ( leaseCarPercent )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "leaseCarPrice"
        ": "
        <
        div
        data-name
        =
        "leaseCarPrice"
        data-type
        =
        "Float?"
        data-updates
        =
        "summary leaseCarAddition "
        >
        ""
        input ( leaseCarPrice )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "monthlySalary"
        ": "
        <
        div
        data-name
        =
        "monthlySalary"
        data-type
        =
        "Float"
        data-updates
        =
        "grossSalary "
        >
        ""
        input ( monthlySalary )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "name"
        ": "
        <
        div
        data-name
        =
        "name"
        data-type
        =
        "String"
        data-updates
        =
        "summary "
        data-default
        =
        "true"
        >
        ""
        input ( name )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "netSalary"
        ": "
        <
        div
        data-name
        =
        "netSalary"
        data-type
        =
        "Float"
        data-updates
        =
        "summary "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getNetSalary() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "netSalaryYear"
        ": "
        <
        div
        data-name
        =
        "netSalaryYear"
        data-type
        =
        "Float"
        data-updates
        =
        "netSalary "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getNetSalaryYear() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "salaryBracket1"
        ": "
        <
        div
        data-name
        =
        "salaryBracket1"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getSalaryBracket1() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "salaryBracket2"
        ": "
        <
        div
        data-name
        =
        "salaryBracket2"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getSalaryBracket2() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "salaryBracket3"
        ": "
        <
        div
        data-name
        =
        "salaryBracket3"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getSalaryBracket3() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "salaryBracket4"
        ": "
        <
        div
        data-name
        =
        "salaryBracket4"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getSalaryBracket4() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "summary"
        ": "
        <
        div
        data-name
        =
        "summary"
        data-type
        =
        "String"
        data-updates
        =
        ""
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getSummary() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "tax"
        ": "
        <
        div
        data-name
        =
        "tax"
        data-type
        =
        "Float"
        data-updates
        =
        "netSalaryYear "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTax() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxableIncome"
        ": "
        <
        div
        data-name
        =
        "taxableIncome"
        data-type
        =
        "Float"
        data-updates
        =
        "salaryBracket3 salaryBracket2 salaryBracket1 gernalTaxDiscount employedTaxDiscount salaryBracket4 "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxableIncome() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxBracket1"
        ": "
        <
        div
        data-name
        =
        "taxBracket1"
        data-type
        =
        "Float"
        data-updates
        =
        "salaryBracket1 salaryBracket2 "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxBracket1() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxBracket2"
        ": "
        <
        div
        data-name
        =
        "taxBracket2"
        data-type
        =
        "Float"
        data-updates
        =
        "salaryBracket3 salaryBracket2 "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxBracket2() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxBracket3"
        ": "
        <
        div
        data-name
        =
        "taxBracket3"
        data-type
        =
        "Float"
        data-updates
        =
        "salaryBracket3 salaryBracket4 "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxBracket3() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxRate1"
        ": "
        <
        div
        data-name
        =
        "taxRate1"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxRate1() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxRate2"
        ": "
        <
        div
        data-name
        =
        "taxRate2"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxRate2() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxRate3"
        ": "
        <
        div
        data-name
        =
        "taxRate3"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxRate3() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "taxRate4"
        ": "
        <
        div
        data-name
        =
        "taxRate4"
        data-type
        =
        "Float"
        data-updates
        =
        "incomeTax "
        >
        <
        div
        class
        =
        "output"
        >
        ""
        output ( temp.getTaxRate4() )
        </
        div
        >
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        ""
        "thirteenthMonth"
        ": "
        <
        div
        data-name
        =
        "thirteenthMonth"
        data-type
        =
        "Boolean"
        data-updates
        =
        "grossSalary "
        data-default
        =
        "true"
        >
        ""
        input ( thirteenthMonth )
        <
        div
        class
        =
        "error-msg"
        style
        =
        "color: red"
        >
        </
        div
        >
        <
        div
        class
        =
        "default-output"
        >
        </
        div
        >
        </
        div
        >
        <
        br
        />
        submit
        action
        {
          if ( holidayAllowance != null )
          {
            temp.holidayAllowance := holidayAllowance;
          }
          else
          {
            temp.holidayAllowance := null;
          }
          temp.leaseCarPercent := leaseCarPercent;
          temp.leaseCarPrice := leaseCarPrice;
          temp.monthlySalary := monthlySalary;
          if ( name.trim() != "" )
          {
            temp.name := name;
          }
          else
          {
            temp.name := null;
          }
          if ( thirteenthMonth != null )
          {
            temp.thirteenthMonth := thirteenthMonth;
          }
          else
          {
            temp.thirteenthMonth := null;
          }
          temp.save();
        }
        [
        ]
        {
        "Save"
        }
        }
    <
    hr
    />
    navigate manageIncome() [ ] { "Back" }
    }
  }