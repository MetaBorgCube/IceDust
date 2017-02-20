import lib.icedust.*;
import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import javax.lang.model.type.NullType;

class incrementalwithsubtype  
{ 
  public static void main(String[] args)
  { 
    Book b = new Book();
    b.setName("my book");
    maintainCaches();
    { 
      String var1 = Book.getTitle(b);
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
      Book.updateAllTitleCache();
      notEmpty = notEmpty || Book.hasDirtyTitle();
    }
  }
}

class Book implements Named 
{ 
  public Book () 
  { 
    Book.flagDirtyTitle(this);
  }

  public void setName(String en)
  { 
    setIncrementalName(en);
  }

  protected void addIncrementalName(String en)
  { 
    setIncrementalName(en);
  }

  protected void removeIncrementalName(String en)
  { 
    setIncrementalName(null);
  }

  protected void setIncrementalName(String en)
  { 
    String oldValue = this.getName();
    this.name = en;
    String
    newValue = this.getName();
    if(!Expressions.nullSafeEqual(oldValue, newValue))
    { 
      dirtyFlagFlowstoName();
    }
  }

  public static String getName(Named en)
  { 
    return en == null ? null : en.getName();
  }

  public static Collection<String> getName(Collection<Named> ens)
  { 
    Collection<String> result = Expressions.emptyCollection();
    for(Named en : ens)
    { 
      if(en.getName() != null)
        result.add(en.getName());
    }
    return result;
  }

  public String getName()
  { 
    return name;
  }

  public void dirtyFlagFlowstoName()
  { 
    { 
      Book var1 = Expressions.filterType(this, Book.class);
      Book.flagDirtyTitle(var1);
    }
  }

  protected String name;

  protected void updateTitle_cache()
  { 
    setCacheTitle(calculateTitle());
  }

  public static boolean hasDirtyTitle()
  { 
    return !dirtyTitle.isEmpty();
  }

  public static void updateAllTitleCache()
  { 
    Collection<Book> ens = dirtyTitle;
    dirtyTitle = new HashSet<Book>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "Book.title" + ": " + ens.size());
    }
    for(Book en : ens)
    { 
      en.updateTitle_cache();
    }
  }

  public void setCacheTitle(String en)
  { 
    setCacheIncrementalTitle(en);
  }

  protected void addCacheIncrementalTitle(String en)
  { 
    setCacheIncrementalTitle(en);
  }

  protected void removeCacheIncrementalTitle(String en)
  { 
    setCacheIncrementalTitle(null);
  }

  protected void setCacheIncrementalTitle(String en)
  { 
    this.cacheTitle = en;
  }

  public static String getTitle(Book en)
  { 
    return en == null ? null : en.getTitle();
  }

  public static Collection<String> getTitle(Collection<Book> ens)
  { 
    Collection<String> result = Expressions.emptyCollection();
    for(Book en : ens)
    { 
      if(en.getTitle() != null)
        result.add(en.getTitle());
    }
    return result;
  }

  public String getTitle()
  { 
    return getCalculatedTitle();
  }

  private String getCalculatedTitle()
  { 
    return cacheTitle;
  }

  private String calculateTitle()
  { 
    String var1 = this.getName();
    return var1;
  }

  public void dirtyFlagFlowstoTitle()
  { }

  protected static void flagDirtyTitle(Book en)
  { 
    if(en != null)
      dirtyTitle.add(en);
  }

  protected static void flagDirtyTitle(Collection<Book> ens)
  { 
    dirtyTitle.addAll(ens);
  }

  protected String cacheTitle;

  private static Collection<Book> dirtyTitle = new HashSet<Book>();
}

interface Named  
{ 
//  public Named () 
//  { }
//
//  public void setName(String en)
//  { 
//    setIncrementalName(en);
//  }
//
//  protected void addIncrementalName(String en)
//  { 
//    setIncrementalName(en);
//  }
//
//  protected void removeIncrementalName(String en)
//  { 
//    setIncrementalName(null);
//  }
//
//  protected void setIncrementalName(String en)
//  { 
//    String oldValue = this.getName();
//    this.name = en;
//    String
//    newValue = this.getName();
//    if(!Expressions.nullSafeEqual(oldValue, newValue))
//    { 
//      dirtyFlagFlowstoName();
//    }
//  }
//
//  public static String getName(Named en)
//  { 
//    return en == null ? null : en.getName();
//  }
//
//  public static Collection<String> getName(Collection<Named> ens)
//  { 
//    Collection<String> result = Expressions.emptyCollection();
//    for(Named en : ens)
//    { 
//      if(en.getName() != null)
//        result.add(en.getName());
//    }
//    return result;
//  }
//
  public String getName();
//  { 
//    return name;
//  }
//
//  public void dirtyFlagFlowstoName()
//  { 
//    { 
//      Book var1 = Expressions.filterType(this, Book.class);
//      Book.flagDirtyTitle(var1);
//    }
//  }
//
//  protected String name;
}