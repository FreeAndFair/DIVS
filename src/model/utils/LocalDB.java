package model.utils;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;

/**
 * Singleton class contains connection to the database
 * 
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class LocalDB {

	private static LocalDB instance;
	private static Connection conn;

	/**
	 * Private constructor to make sure that class 
	 * is singleton
	 * @param jdbc_driver 
	 * @param db_url
	 * @throws DivsException
	 */
	//@ post conn != null;
	//@ assignable conn;
	//@ signals (DivsException d) (d instanceof DivsException);
	private LocalDB (
			/*@ non_null @*/ String jdbc_driver, 
			/*@ non_null @*/ String db_url) throws DivsException {
        try {
        	Class.forName(jdbc_driver);
            conn = DriverManager.
                getConnection(db_url);
            //@ assert conn == null;
        } catch (ClassNotFoundException e) {
        	throw new DivsException(DivsException.DB_CLASS_NOT_FOUND, 
        			""+e.getMessage());
        } catch (SQLException e) {
        	throw new DivsException(DivsException.NO_DB_CONNECTION, 
        			""+e.getMessage());
        }
	}

	/**
	 * Method fetches the instance of the class
	 * @param jdbc_driver JDBC driver of the database
	 * @param db_url URL of the database
	 * @return Returns a connection to the database
	 */
	//@ post instance != null;
	//@ post conn != null;
	//@ assignable instance, conn;
	//@ signals (DivsException d) (d instanceof DivsException);
    public static Connection getConnection(
    		/*@ non_null @*/ String jdbc_driver, 
    		/*@ non_null @*/ String db_url) throws DivsException {
        if (conn == null || instance == null) {
           	instance = new LocalDB(jdbc_driver, db_url);
        }
        return conn;
    }

}