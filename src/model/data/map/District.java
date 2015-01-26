package model.data.map;

import java.io.Serializable;

import model.ElectionConstants;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class District implements Serializable {

	private static final long serialVersionUID = 1L;

	private String name;
	private int district_id;
	private Constituency constituency;

	//@ invariant district_id > 0;
	//@ invariant name != null;
	//@ invariant constituency != null;

	/**
	 * @param district_id District id in the database
	 * @param name Name of the district
	 * @param constituency Constituency to which district belongs
	 */
	//@ pre district_id > 0;
	public District(int district_id, /*@ non_null @*/ String name, 
					/*@ non_null @*/ Constituency constituency) {
		this.district_id = district_id;
		this.name = name;
		this.constituency = constituency;
	}
	
	/**
	 * @return The district id of the district (in the database)
	 */
	public /*@ pure @*/ int getDistrictId() {
		return district_id;
	}

	/**
	 * @return The name of the district
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}

	/**
	 * @return The constituency to which the district belongs
	 */
	public /*@ pure @*/ Constituency getConstituency() {
		return this.constituency;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		@SuppressWarnings("unused")
		int i = ElectionConstants.SEATS_DENMARK; // used to make import come without a warning
		return "District - name: "+name+";constituency: "+constituency.getName();
	}

}