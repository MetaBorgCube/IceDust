package derivations;

import java.util.ArrayList;
import java.util.Map;
import java.util.Set;
import java.util.TimerTask;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;

import utils.AbstractPageServlet;
import utils.GlobalVariables;
import utils.GlobalsPageServlet;
import utils.ThreadLocalOut;
import utils.ThreadLocalPage;

public class Settings {

    static volatile boolean updatesEnabled = true;

    public static boolean getUpdatesEnabled() {
        return updatesEnabled;
    }

    public static void setUpdatesEnabled(boolean setting) {
        updatesEnabled = setting;
    }

    static volatile boolean dirtyFlaggingEnabled = true;

    public static boolean getDirtyFlaggingEnabled() {
        return dirtyFlaggingEnabled;
    }

    public static void setDirtyFlaggingEnabled(boolean setting) {
        dirtyFlaggingEnabled = setting;
    }

    static WorkerSet workers;

    public Settings(int n, int millis, int calcBatchSize) {
        workers = new WorkerSet(millis);
        workers.setNumWorkers(n);
        workers.setCalcBatchSize(calcBatchSize);
    }

    public static void setNumWorkers(int n) {
        workers.setNumWorkers(n);
    }

    public static int getNumWorkers() {
        return workers.getNumWorkers();
    }
    
    public static void setCalcBatchSize(int n) {
        workers.setCalcBatchSize(n);
    }

    public static int getCalcBatchSize() {
        return workers.getCalcBatchSize();
    }
    

    public static boolean getLogincremental() {
        return DirtyCollections.logincremental;
    }

    public static void setLogincremental(boolean setting) {
        DirtyCollections.logincremental = setting;
    }

    public static boolean getLogeventualupdate() {
        return DirtyCollections.logeventualupdate;
    }

    public static void setLogeventualupdate(boolean setting) {
        DirtyCollections.logeventualupdate = setting;
    }

    public static boolean getLogeventualstatus() {
        return DirtyCollections.logeventualstatus;
    }

    public static void setLogeventualstatus(boolean setting) {
        DirtyCollections.logeventualstatus = setting;
    }

    private static Map<Thread, Set<String>> threadFieldMap = new ConcurrentHashMap<Thread, Set<String>>();
    private static Map<Thread, String> threadUuidMap = new ConcurrentHashMap<Thread, String>();

    public static void threadMapsSet(Thread t, Set<String> hashmap, String uuid) {
        threadFieldMap.put(t, hashmap);
        threadUuidMap.put(t, uuid);
    }

    public static void reschedule(Thread t) {
        Set<String> hashmap = threadFieldMap.get(t);
        String uuid = threadUuidMap.get(t);
        hashmap.add(uuid);
        DirtyCollections.dirtyI(0);
    }

}

class WorkerSet {

    private int numWorkers = 0;
    private int batchSize = 1;
    private int checkInterval;
    private ScheduledExecutorService ex = Executors.newScheduledThreadPool(16); // is maxThreads
    private ArrayList<ScheduledFuture<?>> schedules = new ArrayList<ScheduledFuture<?>>();

    public WorkerSet(int checkInterval) {
        this.checkInterval = checkInterval;
    }

    public void setNumWorkers(int numWorkers) {
        int oldNumWorkers = schedules.size();
        this.numWorkers = numWorkers;
        if (numWorkers > oldNumWorkers) {
            for (int i = oldNumWorkers; i < numWorkers; i++) {
                addWorker(i);
            }
        }
        if (numWorkers < oldNumWorkers) {
            for (int i = oldNumWorkers - 1; i >= numWorkers; i--) {
                removeWorker(i);
            }
        }
    }

    public int getNumWorkers() {
        return numWorkers;
    }
    
    public void setCalcBatchSize(int batchSize) {
        this.batchSize = Math.min(batchSize, 100);
    }

    public int getCalcBatchSize() {
    	    return this.batchSize;
    }

    private void addWorker(int index) {
        if (schedules.size() <= index) {
            System.out.println("Adding Worker " + index);
            TimerTask task = newTask(index);
            ScheduledFuture<?> schedule = ex.scheduleWithFixedDelay(task, 0, checkInterval, TimeUnit.MILLISECONDS);
            schedules.add(index, schedule);
        }
    }

    private TimerTask newTask(final int index) {
        return new java.util.TimerTask() {
            public void run() {
                Thread thisThread = Thread.currentThread();

                while (DirtyCollections.getI() < 2147483647 && Settings.getUpdatesEnabled()) {
                    if (numWorkers <= index) {
                        System.out.println("Worker " + index + ": shutting down");
                        break;
                    }

                    if (utils.GlobalVariables.globalvarsChecked && utils.GlobalInit.initChecked) {
                        org.hibernate.Session hibSession = null;
                        try {
                            org.webdsl.servlet.ServletState.scheduledTaskStarted(
                                    "invoke updateDerivationsAsync() every x milliseconds with y threads");
                            AbstractPageServlet ps = new GlobalsPageServlet();
                            ThreadLocalPage.set(ps);
                            ps.initRequestVars();
                            hibSession = utils.HibernateUtil.getCurrentSession();
                            hibSession.beginTransaction();
                            if (GlobalVariables.initGlobalVars(ps.envGlobalAndSession,
                                    utils.HibernateUtil.getCurrentSession())) {
                                int numCalcs = batchSize;
                                while( 0 < numCalcs-- ) {
                                	   DirtyCollections.incrementCalculation();
                                    webdsl.generated.functions.updateDerivationsAsyncThread_
                                        .updateDerivationsAsyncThread_(thisThread);
                                }
                                utils.HibernateUtil.getCurrentSession().getTransaction().commit();
                                ps.invalidatePageCacheIfNeeded();
                            }
                        } catch (org.hibernate.StaleStateException
                                | org.hibernate.exception.LockAcquisitionException ex) {
//                            org.webdsl.logging.Logger
//                                    .error("updateDerivationsAsync() database collision, rescheduling");

                            DirtyCollections.incrementCollision();
                          
                            Settings.reschedule(thisThread);

                            utils.HibernateUtil.getCurrentSession().getTransaction().rollback();
                        } catch (org.hibernate.ObjectNotFoundException ex) {
                          // happens in two cases: objects get deleted but are still in queue, or objects are created and are in queue but creation-transaction fails
                          DirtyCollections.incrementNotFound();
                        
                          utils.HibernateUtil.getCurrentSession().getTransaction().rollback();
                        } catch (Exception ex) {
                            org.webdsl.logging.Logger.error(ex.getClass().getCanonicalName());
                            org.webdsl.logging.Logger.error("exception occured while executing timed function: "
                                    + "invoke updateDerivationsAsync() every x milliseconds");
                            org.webdsl.logging.Logger.error("exception message: " + ex.getMessage(), ex);
                            utils.HibernateUtil.getCurrentSession().getTransaction().rollback();
                        } finally {
                            org.webdsl.servlet.ServletState.scheduledTaskEnded();
                            ThreadLocalPage.set(null);
                        }
                    }
                }
            }
        };
    }

    private void removeWorker(int index) {
        if (schedules.get(index) != null) {
            System.out.println("Removing Worker " + index);
            schedules.get(index).cancel(false);
            schedules.remove(index);
        }
    }

    public void shutdown() {
        setNumWorkers(0);
        ex.shutdown();
    }
}
