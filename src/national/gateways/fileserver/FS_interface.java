package national.gateways.fileserver;

import national.utils.DivsException;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ interface FS_interface {

	/**
	 * Method enables registered voter to vote through a web server 
	 * by storing the vote as a file on file system  
	 * @param vote String that represents the vote of the voter
	 * @throws DivsException Throws exception when something is wrong with e.g. read/write rights on file system
	 */
	public void store_vote(String vote) throws DivsException;

	/**
	 * Method retrieves a vote from the file system
	 * @param voter_id The id of the voter
	 * @return A string representing a vote
	 * @throws DivsException Throws exception when something is wrong with e.g. read/write rights on file system
	 */
	public String retrieve_vote(int voter_id) throws DivsException;

}