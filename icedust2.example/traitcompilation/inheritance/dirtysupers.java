import lib.icedust.*;
import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import javax.lang.model.type.NullType;

class dirtysupers  
{ 
  public static void main(String[] args)
  { 
    UseCountTen2 twenty = new UseCountTen2();
    maintainCaches();
    { 
      Integer var1 = UseCountTen2.getTen(twenty);
      System.out.println(var1);
    }
    { 
      Integer var1 = UseCountTen2.getTwenty(twenty);
      System.out.println(var1);
    }
    { 
      Integer var1 = UseCountTen2.getThirty(twenty);
      System.out.println(var1);
    }
    twenty.setCacheTen(100);
    maintainCaches();
    { 
      Integer var1 = UseCountTen2.getTen(twenty);
      System.out.println(var1);
    }
    { 
      Integer var1 = UseCountTen2.getTwenty(twenty);
      System.out.println(var1);
    }
    { 
      Integer var1 = UseCountTen2.getThirty(twenty);
      System.out.println(var1);
    }
  }

  private static void maintainCaches()
  { 
    boolean notEmpty;
    notEmpty = true;
    while(notEmpty)
    { 
      notEmpty = false;
      CountTen2.updateAllTenCache();
      notEmpty = notEmpty || CountTen2.hasDirtyTen();
    }
    notEmpty = true;
    while(notEmpty)
    { 
      notEmpty = false;
      CountTen2.updateAllThirtyCache();
      notEmpty = notEmpty || CountTen2.hasDirtyThirty();
    }
    notEmpty = true;
    while(notEmpty)
    { 
      notEmpty = false;
      UseCountTen2.updateAllTwentyCache();
      notEmpty = notEmpty || UseCountTen2.hasDirtyTwenty();
    }
  }
}

class CountTen2  
{ 
  public CountTen2 () 
  { 
    CountTen2.flagDirtyTen(this);
    CountTen2.flagDirtyThirty(this);
  }

  protected void updateTen_cache()
  { 
    setCacheTen(calculateTen());
  }

  public static boolean hasDirtyTen()
  { 
    return !dirtyTen.isEmpty();
  }

  public static void updateAllTenCache()
  { 
    Collection<CountTen2> ens = dirtyTen;
    dirtyTen = new HashSet<CountTen2>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "CountTen2.ten" + ": " + ens.size());
    }
    for(CountTen2 en : ens)
    { 
      en.updateTen_cache();
    }
  }

  public void setCacheTen(Integer en)
  { 
    setCacheIncrementalTen(en);
  }

  protected void addCacheIncrementalTen(Integer en)
  { 
    setCacheIncrementalTen(en);
  }

  protected void removeCacheIncrementalTen(Integer en)
  { 
    setCacheIncrementalTen(null);
  }

  protected void setCacheIncrementalTen(Integer en)
  { 
    Integer oldValue = this.getTen();
    this.cacheTen = en;
    Integer
    newValue = this.getTen();
    if(!Expressions.nullSafeEqual(oldValue, newValue))
    { 
      dirtyFlagFlowstoTen();
    }
  }

  public static Integer getTen(CountTen2 en)
  { 
    return en == null ? null : en.getTen();
  }

  public static Collection<Integer> getTen(Collection<CountTen2> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(CountTen2 en : ens)
    { 
      if(en.getTen() != null)
        result.add(en.getTen());
    }
    return result;
  }

  public Integer getTen()
  { 
    return getCalculatedTen();
  }

  private Integer getCalculatedTen()
  { 
    return cacheTen;
  }

  private Integer calculateTen()
  { 
    Integer var1 = Expressions.plus_Integer(1, 2);
    Integer var2 = Expressions.plus_Integer(var1, 3);
    Integer var3 = Expressions.plus_Integer(var2, 4);
    return var3;
  }

  public void dirtyFlagFlowstoTen()
  { 
    { 
      CountTen2.flagDirtyThirty(this);
    }
  }

  protected static void flagDirtyTen(CountTen2 en)
  { 
    if(en != null)
      dirtyTen.add(en);
  }

  protected static void flagDirtyTen(Collection<CountTen2> ens)
  { 
    dirtyTen.addAll(ens);
  }

  protected Integer cacheTen;

  private static Collection<CountTen2> dirtyTen = new HashSet<CountTen2>();

  protected void updateThirty_cache()
  { 
    setCacheThirty(calculateThirty());
  }

  public static boolean hasDirtyThirty()
  { 
    return !dirtyThirty.isEmpty();
  }

  public static void updateAllThirtyCache()
  { 
    Collection<CountTen2> ens = dirtyThirty;
    dirtyThirty = new HashSet<CountTen2>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "CountTen2.thirty" + ": " + ens.size());
    }
    for(CountTen2 en : ens)
    { 
      en.updateThirty_cache();
    }
  }

  public void setCacheThirty(Integer en)
  { 
    setCacheIncrementalThirty(en);
  }

  protected void addCacheIncrementalThirty(Integer en)
  { 
    setCacheIncrementalThirty(en);
  }

  protected void removeCacheIncrementalThirty(Integer en)
  { 
    setCacheIncrementalThirty(null);
  }

  protected void setCacheIncrementalThirty(Integer en)
  { 
    this.cacheThirty = en;
  }

  public static Integer getThirty(CountTen2 en)
  { 
    return en == null ? null : en.getThirty();
  }

  public static Collection<Integer> getThirty(Collection<CountTen2> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(CountTen2 en : ens)
    { 
      if(en.getThirty() != null)
        result.add(en.getThirty());
    }
    return result;
  }

  public Integer getThirty()
  { 
    return getCalculatedThirty();
  }

  private Integer getCalculatedThirty()
  { 
    return cacheThirty;
  }

  private Integer calculateThirty()
  { 
    Integer var1 = this.getTen();
    Integer var2 = Expressions.mul_Integer(var1, 3);
    return var2;
  }

  public void dirtyFlagFlowstoThirty()
  { }

  protected static void flagDirtyThirty(CountTen2 en)
  { 
    if(en != null)
      dirtyThirty.add(en);
  }

  protected static void flagDirtyThirty(Collection<CountTen2> ens)
  { 
    dirtyThirty.addAll(ens);
  }

  protected Integer cacheThirty;

  private static Collection<CountTen2> dirtyThirty = new HashSet<CountTen2>();
}

class UseCountTen2 extends CountTen2
{ 
  public UseCountTen2 () 
  { 
    UseCountTen2.flagDirtyTen(this);
    CountTen2.flagDirtyThirty(this);
    UseCountTen2.flagDirtyTwenty(this);
  }

//  protected void updateTen_cache()
//  { 
//    setCacheTen(calculateTen());
//  }
//
//  public static boolean hasDirtyTen()
//  { 
//    return !dirtyTen.isEmpty();
//  }
//
//  public static void updateAllTenCache()
//  { 
//    Collection<UseCountTen2> ens = dirtyTen;
//    dirtyTen = new HashSet<UseCountTen2>();
//    if(ens.size() > 0)
//    { 
//      System.out.println("Updating " + "UseCountTen2.ten" + ": " + ens.size());
//    }
//    for(UseCountTen2 en : ens)
//    { 
//      en.updateTen_cache();
//    }
//  }
//
//  public void setCacheTen(Integer en)
//  { 
//    setCacheIncrementalTen(en);
//  }
//
//  protected void addCacheIncrementalTen(Integer en)
//  { 
//    setCacheIncrementalTen(en);
//  }
//
//  protected void removeCacheIncrementalTen(Integer en)
//  { 
//    setCacheIncrementalTen(null);
//  }
//
//  protected void setCacheIncrementalTen(Integer en)
//  { 
//    Integer oldValue = this.getTen();
//    this.cacheTen = en;
//    Integer
//    newValue = this.getTen();
//    if(!Expressions.nullSafeEqual(oldValue, newValue))
//    { 
//      dirtyFlagFlowstoTen();
//    }
//  }

//  public static Integer getTen(UseCountTen2 en)
//  { 
//    return en == null ? null : en.getTen();
//  }
//
//  public static Collection<Integer> getTen(Collection<UseCountTen2> ens)
//  { 
//    Collection<Integer> result = Expressions.emptyCollection();
//    for(UseCountTen2 en : ens)
//    { 
//      if(en.getTen() != null)
//        result.add(en.getTen());
//    }
//    return result;
//  }

  public Integer getTen()
  { 
    return getCalculatedTen();
  }

  private Integer getCalculatedTen()
  { 
    return cacheTen;
  }

  private Integer calculateTen()
  { 
    return 10;
  }

  public void dirtyFlagFlowstoTen()
  { 
    super.dirtyFlagFlowstoTen();
    { 
      UseCountTen2.flagDirtyTwenty(this);
    }
  }

//  protected static void flagDirtyTen(UseCountTen2 en)
//  { 
//    if(en != null)
//      dirtyTen.add(en);
//  }
//
//  protected static void flagDirtyTen(Collection<UseCountTen2> ens)
//  { 
//    dirtyTen.addAll(ens);
//  }

//  protected Integer cacheTen;

//  private static Collection<UseCountTen2> dirtyTen = new HashSet<UseCountTen2>();

  protected void updateThirty_cache()
  { 
    setCacheThirty(calculateThirty());
  }

  public static boolean hasDirtyThirty()
  { 
    return !dirtyThirty.isEmpty();
  }

  public static void updateAllThirtyCache()
  { 
    Collection<CountTen2> ens = dirtyThirty;
    dirtyThirty = new HashSet<CountTen2>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "CountTen2.thirty" + ": " + ens.size());
    }
    for(CountTen2 en : ens)
    { 
      en.updateThirty_cache();
    }
  }

  public void setCacheThirty(Integer en)
  { 
    setCacheIncrementalThirty(en);
  }

  protected void addCacheIncrementalThirty(Integer en)
  { 
    setCacheIncrementalThirty(en);
  }

  protected void removeCacheIncrementalThirty(Integer en)
  { 
    setCacheIncrementalThirty(null);
  }

  protected void setCacheIncrementalThirty(Integer en)
  { 
    this.cacheThirty = en;
  }

  public static Integer getThirty(CountTen2 en)
  { 
    return en == null ? null : en.getThirty();
  }

  public static Collection<Integer> getThirty(Collection<CountTen2> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(CountTen2 en : ens)
    { 
      if(en.getThirty() != null)
        result.add(en.getThirty());
    }
    return result;
  }

  public Integer getThirty()
  { 
    return getCalculatedThirty();
  }

  private Integer getCalculatedThirty()
  { 
    return cacheThirty;
  }

  private Integer calculateThirty()
  { 
    Integer var1 = this.getTen();
    Integer var2 = Expressions.mul_Integer(var1, 3);
    return var2;
  }

  public void dirtyFlagFlowstoThirty()
  { }

  protected static void flagDirtyThirty(CountTen2 en)
  { 
    if(en != null)
      dirtyThirty.add(en);
  }

  protected static void flagDirtyThirty(Collection<CountTen2> ens)
  { 
    dirtyThirty.addAll(ens);
  }

  protected Integer cacheThirty;

  private static Collection<CountTen2> dirtyThirty = new HashSet<CountTen2>();

  protected void updateTwenty_cache()
  { 
    setCacheTwenty(calculateTwenty());
  }

  public static boolean hasDirtyTwenty()
  { 
    return !dirtyTwenty.isEmpty();
  }

  public static void updateAllTwentyCache()
  { 
    Collection<UseCountTen2> ens = dirtyTwenty;
    dirtyTwenty = new HashSet<UseCountTen2>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "UseCountTen2.twenty" + ": " + ens.size());
    }
    for(UseCountTen2 en : ens)
    { 
      en.updateTwenty_cache();
    }
  }

  public void setCacheTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(en);
  }

  protected void addCacheIncrementalTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(en);
  }

  protected void removeCacheIncrementalTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(null);
  }

  protected void setCacheIncrementalTwenty(Integer en)
  { 
    this.cacheTwenty = en;
  }

  public static Integer getTwenty(UseCountTen2 en)
  { 
    return en == null ? null : en.getTwenty();
  }

  public static Collection<Integer> getTwenty(Collection<UseCountTen2> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(UseCountTen2 en : ens)
    { 
      if(en.getTwenty() != null)
        result.add(en.getTwenty());
    }
    return result;
  }

  public Integer getTwenty()
  { 
    return getCalculatedTwenty();
  }

  private Integer getCalculatedTwenty()
  { 
    return cacheTwenty;
  }

  private Integer calculateTwenty()
  { 
    Integer var1 = this.getTen();
    Integer var2 = Expressions.mul_Integer(var1, 2);
    return var2;
  }

  public void dirtyFlagFlowstoTwenty()
  { }

  protected static void flagDirtyTwenty(UseCountTen2 en)
  { 
    if(en != null)
      dirtyTwenty.add(en);
  }

  protected static void flagDirtyTwenty(Collection<UseCountTen2> ens)
  { 
    dirtyTwenty.addAll(ens);
  }

  protected Integer cacheTwenty;

  private static Collection<UseCountTen2> dirtyTwenty = new HashSet<UseCountTen2>();
}