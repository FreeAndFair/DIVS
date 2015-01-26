package national.data.map;

import java.io.Serializable;
import national.ElectionConstants;


/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Province implements Serializable {
	
	private static final long serialVersionUID = 1L;

	private int province_id;
	private String name;
	private int constituency_seats, additional_seats;

	//@ invariant province_id > 0;
	//@ invariant name != null;
	//@ invariant constituency_seats >= 0;
	//@ invariant constituency_seats <= ElectionConstants.CONSTITUENCY_SEATS;
	//@ invariant 0 <= additional_seats;
	//@ invariant additional_seats <= ElectionConstants.ADDITIONAL_SEATS;
	
	/**
	 * @param province_id Province_id of the province in the database
	 * @param name Name of the province
	 * @param constituency_seats No of constituency seats allocated to province
	 * @param additional_seats No of additional seats allocated to province
	 */
	//@ pre province_id > 0;
	//@ pre constituency_seats >= 0;
	//@ pre constituency_seats <= ElectionConstants.CONSTITUENCY_SEATS;
	//@ pre additional_seats >= 0;
	//@ pre additional_seats <= ElectionConstants.ADDITIONAL_SEATS;
	public Province(int province_id, /*@ non_null @*/ String name, 
			int constituency_seats, int additional_seats) {
		this.province_id = province_id;
		this.name = name;
		this.constituency_seats = constituency_seats;
		this.additional_seats = additional_seats;
	}

	/**
	 * @return The id of the province
	 */
	public /*@ pure @*/ int getProvinceId() {
		return province_id;
	}

	/**
	 * @return The name of the province
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}

	/**
	 * @return The no of constituency seats belonging to province
	 */
	public /*@ pure @*/ int getConstituencySeats() {
		return constituency_seats;
	}

	/**
	 * @return The no of additional seats belonging to province
	 */
	public /*@ pure @*/ int getAdditionalSeats() {
		return additional_seats;
	}
	
	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		@SuppressWarnings("unused")
		int i = ElectionConstants.SEATS_FAROE_ISLANDS; //used to make import come without a warning
		return "Province - name: "+name+";constituency seats: "+constituency_seats+";additional seats: "+additional_seats;
	}
}